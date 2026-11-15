# -*- coding: utf-8 -*-
"""
SEDAYU SCALPING BOT
Fitur Lengkap:
- Konfigurasi terpisah di config.json & token.txt
- Saklar tunggal LIVE_MODE (True = Live Senin-Jumat | False = Tes Akhir Pekan/Malam)
- Pengaman Anti-Banned: 5 Worker, Jitter acak, Global Rate-Limit Pause (HTTP 429)
- Dual-Lane Scanner: Slow-Lane (20 saham tiap 10s) + Fast-Lane Paralel (pantauan 2.0s serentak untuk 3 sinyal aktif)
- Filter Spread Ketat (maksimal 1 tick), Verifikasi Kilat 2 Detik anti spoofing, & Pullback berbasis Support VWAP
- Kontrol Jarak Jauh via Telegram: /status, /pause, /resume, /pagi
"""

import json
import os
import random
import re
import signal
import sqlite3
import sys
import threading
import time
import uuid
from collections import defaultdict, deque
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import datetime, date, time as dtime, timezone, timedelta
from typing import Any, Dict, List, Optional, Tuple

import requests

# ============================================================================
# SAKLAR UTAMA & KONFIGURASI KECEPATAN
# ============================================================================

LIVE_MODE = False                 # False = Mode Tes (Langsung kirim Morning Watchlist & bypass jam bursa)

# Cakupan & Kecepatan Scan Seimbang (Titik Tengah Cepat & Aman)
MODE_CAKUPAN = "TOP_N"            # TOP_N (ambil maksimal MAX_SAHAM dari screener) | ALL | CUSTOM (watchlist.txt)
MAX_SAHAM = 20                    # Fokus 20 saham paling likuid teratas
JUMLAH_WORKER = 5                 # 5 jalur paralel (±1.2 detik per siklus 20 saham)
SCAN_INTERVAL_SECONDS = 10 if LIVE_MODE else 6
FAST_LANE_INTERVAL_SECONDS = 2.0  # Pantauan cepat 2 detik serentak khusus sinyal aktif (⏳ / 🚀)
MAX_ACTIVE_SIGNALS = 4            # Batasi maksimal 3 sinyal aktif bersamaan agar Fast-Lane tetap ringan
UPDATE_SCREENER_SECONDS = 90      # Update screener tiap 1.5 menit
REQUEST_TIMEOUT_SECONDS = 12
HTTP_RETRIES = 2

# Parameter Strategi Otomatis (Mengikuti LIVE_MODE)
COOLDOWN_SECONDS = 180
MIN_WALL_LOT = 5000
MIN_DAILY_VALUE_IDR = 2_000_000_000
MAX_SIGNAL_AGE_SECONDS = 900      # Maksimal 15 menit (otomatis dipangkas jika mendekati 15:50 WIB)
MAX_GAIN_WARNING_PERCENT = 15.0   # Peringatan pucuk jika kenaikan >= 15%

if LIVE_MODE:
    MIN_BID_SUPPORT_LOT = 2000
    MIN_BID_TO_WALL_RATIO = 0.60  # Minimal total Bid 1+2 = 60% dari tebal tembok Offer agar siap dorong
    MIN_PULLBACK_RANGE_PERCENT = 4.0
    MAX_VWAP_DISTANCE_ENTRY_PERCENT = 1.5
    MAX_PULLBACK_VWAP_DISTANCE_PERCENT = 1.2
    PULLBACK_BOUNCE_SAMPLES = 3
else:
    MIN_BID_SUPPORT_LOT = 10
    MIN_BID_TO_WALL_RATIO = 0.0
    MIN_PULLBACK_RANGE_PERCENT = 0.5
    MAX_VWAP_DISTANCE_ENTRY_PERCENT = 1.5
    MAX_PULLBACK_VWAP_DISTANCE_PERCENT = 10.0
    PULLBACK_BOUNCE_SAMPLES = 3

ORDERBOOK_VOLUME_UNIT = "shares"
DAILY_VOLUME_UNIT = "shares"

DB_FILENAME = "sedayu_live.sqlite3" if LIVE_MODE else "sedayu_test.sqlite3"
LOG_FILENAME = "sedayu_live.log" if LIVE_MODE else "sedayu_test.log"

WIB = timezone(timedelta(hours=7))
LOCK = threading.RLock()
THREAD_LOCAL = threading.local()
AUTH_EXPIRED = threading.Event()
STOP_EVENT = threading.Event()
SCAN_PAUSED = threading.Event()
BLACKLIST_402 = set()
RATE_LIMIT_UNTIL = 0.0
CURRENT_WATCHLIST_SHARED: List[str] = []

PRICE_HISTORY: Dict[str, deque] = defaultdict(lambda: deque(maxlen=60))
TICK_CACHE: Dict[str, Tuple[str, int, str]] = {}


# ============================================================================
# PATH, LOGGING, FILE CONFIG (config.json & token.txt)
# ============================================================================

def base_dir() -> str:
    if getattr(sys, "frozen", False):
        return os.path.dirname(sys.executable)
    return os.path.dirname(os.path.abspath(__file__))


def path_of(name: str) -> str:
    return os.path.join(base_dir(), name)


def log(message: str) -> None:
    stamp = datetime.now(WIB).strftime("%Y-%m-%d %H:%M:%S")
    line = f"[{stamp} WIB] {message}"
    print(line, flush=True)
    try:
        with open(path_of(LOG_FILENAME), "a", encoding="utf-8") as f:
            f.write(line + "\n")
    except Exception:
        pass


def load_app_config() -> Dict[str, str]:
    config_path = path_of("config.json")
    env_tg = os.environ.get("TELEGRAM_TOKEN", "").strip()
    env_chat = os.environ.get("CHAT_ID", "").strip()
    env_scr = os.environ.get("SCREENER_URL", "").strip()
    env_scr2 = os.environ.get("SCREENER_URL_2", "").strip()
    env_admin = os.environ.get("ADMIN_ID", "").strip()

    default_config = {
        "telegram_token": env_tg,
        "chat_id": env_chat,
        "admin_id": env_admin,
        "screener_url": env_scr or "https://stockbit.com",
        "screener_url_2": env_scr2,
    }
    if os.path.exists(config_path):
        try:
            with open(config_path, "r", encoding="utf-8") as f:
                loaded = json.load(f)
            if isinstance(loaded, dict):
                return {
                    "telegram_token": env_tg or str(loaded.get("telegram_token") or "").strip(),
                    "chat_id": env_chat or str(loaded.get("chat_id") or "").strip(),
                    "admin_id": env_admin or str(loaded.get("admin_id") or "").strip(),
                    "screener_url": env_scr or str(loaded.get("screener_url") or default_config["screener_url"]).strip(),
                    "screener_url_2": env_scr2 or str(loaded.get("screener_url_2") or "").strip(),
                }
        except Exception as exc:
            log(f"Gagal membaca config.json ({exc}).")
    return default_config

def load_bearer_token() -> str:
    env_bearer = os.environ.get("BEARER_TOKEN", "").strip()
    if env_bearer:
        return env_bearer[7:].strip() if env_bearer.lower().startswith("bearer ") else env_bearer

    token_path = path_of("token.txt")
    if not os.path.exists(token_path):
        return ""
    with open(token_path, "r", encoding="utf-8") as f:
        token = f.read().strip()
    if token.lower().startswith("bearer "):
        token = token[7:].strip()
    return "" if token == "PASTE_BEARER_TOKEN_STOCKBIT_DI_SINI" else token


def load_symbol_file(filename: str, default: Optional[List[str]] = None) -> List[str]:
    file_path = path_of(filename)
    if not os.path.exists(file_path):
        if default is not None:
            with open(file_path, "w", encoding="utf-8") as f:
                f.write(", ".join(default) + "\n")
            return default[:]
        with open(file_path, "w", encoding="utf-8") as f:
            f.write("# Satu simbol per baris atau pisahkan dengan koma\n")
        return []
    try:
        with open(file_path, "r", encoding="utf-8") as f:
            raw = f.read()
        symbols = [x.strip().upper() for x in re.split(r"[,\n;\s]+", raw) if x.strip()]
        return [x for x in symbols if re.fullmatch(r"[A-Z0-9]{4,6}", x)]
    except Exception as exc:
        log(f"Gagal membaca {filename}: {exc}")
        return default[:] if default else []


def load_holidays() -> set:
    file_path = path_of("hari_libur.txt")
    if not os.path.exists(file_path):
        with open(file_path, "w", encoding="utf-8") as f:
            f.write("# Isi tanggal libur bursa, format YYYY-MM-DD, satu tanggal per baris.\n")
        return set()
    holidays = set()
    with open(file_path, "r", encoding="utf-8") as f:
        for line in f:
            value = line.split("#", 1)[0].strip()
            if not value:
                continue
            try:
                holidays.add(date.fromisoformat(value))
            except ValueError:
                log(f"Format tanggal di hari_libur.txt diabaikan: {value}")
    return holidays


APP_CONFIG = load_app_config()
TELEGRAM_TOKEN = APP_CONFIG["telegram_token"]
CHAT_ID = APP_CONFIG["chat_id"]
SCREENER_URL = APP_CONFIG["screener_url"]
SCREENER_URL_2 = APP_CONFIG.get("screener_url_2", "")
TOPIC_ID = int(os.environ.get("TOPIC_ID", "0") or 0)
TOPIC_WINRATE_ID = int(os.environ.get("TOPIC_WINRATE_ID", "0") or 0)
ADMIN_ID = APP_CONFIG["admin_id"]
MONTHLY_PIN_ID = int(os.environ.get("MONTHLY_PIN_ID", "0") or 0)

BEARER_TOKEN = load_bearer_token()
WATCHLIST_FALLBACK = load_symbol_file("watchlist.txt", ["BAJA", "COIN", "MPIX", "MSIN", "PYFA"])
EXCLUDED_SYMBOLS = set(load_symbol_file("exclude_symbols.txt"))
HOLIDAYS = load_holidays()

HEADERS = {
    "Authorization": f"Bearer {BEARER_TOKEN}",
    "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36",
    "Accept": "application/json, text/plain, */*",
    "Origin": "https://stockbit.com",
    "Referer": "https://stockbit.com",
}


def get_session() -> requests.Session:
    session = getattr(THREAD_LOCAL, "session", None)
    if session is None:
        session = requests.Session()
        session.headers.update(HEADERS)
        THREAD_LOCAL.session = session
    with LOCK:
        session.headers["Authorization"] = HEADERS["Authorization"]
    return session

# ============================================================================
# SQLITE PERSISTENCE
# ============================================================================

class SignalStore:
    def __init__(self, db_path: str):
        self.conn = sqlite3.connect(db_path, check_same_thread=False, timeout=20)
        self.conn.row_factory = sqlite3.Row
        self.lock = threading.RLock()
        with self.lock:
            self.conn.execute("PRAGMA journal_mode=WAL")
            self.conn.execute("PRAGMA synchronous=NORMAL")
            self.conn.executescript(
                """
                CREATE TABLE IF NOT EXISTS signals (
                    signal_id TEXT PRIMARY KEY,
                    signal_key TEXT NOT NULL,
                    symbol TEXT NOT NULL,
                    kind TEXT NOT NULL,
                    status TEXT NOT NULL,
                    created_at REAL NOT NULL,
                    updated_at REAL NOT NULL,
                    closed_at REAL,
                    message_id INTEGER,
                    state_json TEXT NOT NULL
                );
                CREATE INDEX IF NOT EXISTS idx_signals_active ON signals(status, symbol);
                CREATE INDEX IF NOT EXISTS idx_signals_key_time ON signals(signal_key, created_at);
                CREATE TABLE IF NOT EXISTS events (
                    event_id INTEGER PRIMARY KEY AUTOINCREMENT,
                    signal_id TEXT NOT NULL,
                    event_time REAL NOT NULL,
                    event TEXT NOT NULL,
                    note TEXT
                );
                CREATE TABLE IF NOT EXISTS reports (
                    report_date TEXT PRIMARY KEY,
                    sent_at REAL NOT NULL
                );
                CREATE TABLE IF NOT EXISTS daily_refs (
                    symbol TEXT NOT NULL,
                    ref_date TEXT NOT NULL,
                    ref_price REAL NOT NULL,
                    tick INTEGER NOT NULL,
                    source TEXT NOT NULL,
                    PRIMARY KEY(symbol, ref_date)
                );
                """
            )
            self.conn.commit()

    def save_signal(self, state: Dict[str, Any]) -> None:
        now = time.time()
        with self.lock:
            self.conn.execute(
                """INSERT INTO signals(signal_id,signal_key,symbol,kind,status,created_at,updated_at,closed_at,message_id,state_json)
                   VALUES(?,?,?,?,?,?,?,?,?,?)
                   ON CONFLICT(signal_id) DO UPDATE SET status=excluded.status, updated_at=excluded.updated_at,
                   closed_at=excluded.closed_at, message_id=excluded.message_id, state_json=excluded.state_json""",
                (
                    state["signal_id"], state["signal_key"], state["symbol"], state["kind"],
                    state["status"], state["created_at"], now, state.get("closed_at"),
                    state.get("message_id"), json.dumps(state, ensure_ascii=False),
                ),
            )
            self.conn.commit()

    def active_signals(self, symbol: Optional[str] = None) -> List[Dict[str, Any]]:
        with self.lock:
            if symbol:
                rows = self.conn.execute(
                    "SELECT state_json FROM signals WHERE status IN ('ACTIVE','WAIT_ENTRY','WAIT_BREAKOUT') AND symbol=?",
                    (symbol,),
                ).fetchall()
            else:
                rows = self.conn.execute(
                    "SELECT state_json FROM signals WHERE status IN ('ACTIVE','WAIT_ENTRY','WAIT_BREAKOUT')"
                ).fetchall()
        result = []
        for row in rows:
            try:
                result.append(json.loads(row["state_json"]))
            except Exception:
                continue
        return result

    def active_count(self) -> int:
        with self.lock:
            row = self.conn.execute(
                "SELECT COUNT(*) AS n FROM signals WHERE status IN ('ACTIVE','WAIT_ENTRY','WAIT_BREAKOUT')"
            ).fetchone()
            return int(row["n"]) if row else 0

    def has_active(self, symbol: str, kind: str) -> bool:
        with self.lock:
            row = self.conn.execute(
                "SELECT 1 FROM signals WHERE symbol=? AND kind=? AND status IN ('ACTIVE','WAIT_ENTRY','WAIT_BREAKOUT') LIMIT 1",
                (symbol, kind),
            ).fetchone()
            return row is not None

    def has_recent_key(self, signal_key: str, seconds: int) -> bool:
        with self.lock:
            row = self.conn.execute(
                "SELECT 1 FROM signals WHERE signal_key=? AND created_at>=? LIMIT 1",
                (signal_key, time.time() - seconds),
            ).fetchone()
            return row is not None

    def event(self, signal_id: str, name: str, note: str = "") -> None:
        with self.lock:
            self.conn.execute(
                "INSERT INTO events(signal_id,event_time,event,note) VALUES(?,?,?,?)",
                (signal_id, time.time(), name, note),
            )
            self.conn.commit()

    def close_signal(self, state: Dict[str, Any], final_status: str, note: str = "") -> None:
        state["status"] = final_status
        state["closed_at"] = time.time()
        state["updated_at"] = state["closed_at"]
        self.save_signal(state)
        self.event(state["signal_id"], final_status, note)

    def get_tick_ref(self, symbol: str, today: str) -> Optional[Tuple[float, int, str]]:
        with self.lock:
            row = self.conn.execute(
                "SELECT ref_price,tick,source FROM daily_refs WHERE symbol=? AND ref_date=?",
                (symbol, today),
            ).fetchone()
        if row:
            return float(row["ref_price"]), int(row["tick"]), str(row["source"])
        return None

    def set_tick_ref(self, symbol: str, today: str, ref_price: float, tick: int, source: str) -> None:
        with self.lock:
            self.conn.execute(
                "INSERT OR REPLACE INTO daily_refs(symbol,ref_date,ref_price,tick,source) VALUES(?,?,?,?,?)",
                (symbol, today, ref_price, tick, source),
            )
            self.conn.commit()

    def report_sent(self, report_date: str) -> bool:
        with self.lock:
            row = self.conn.execute("SELECT 1 FROM reports WHERE report_date=?", (report_date,)).fetchone()
        return row is not None

    def mark_report_sent(self, report_date: str) -> None:
        with self.lock:
            self.conn.execute("INSERT OR REPLACE INTO reports(report_date,sent_at) VALUES(?,?)", (report_date, time.time()))
            self.conn.commit()

    def daily_stats(self, day: date) -> Dict[str, int]:
        start = datetime.combine(day, dtime.min, WIB).timestamp()
        end = datetime.combine(day + timedelta(days=1), dtime.min, WIB).timestamp()
        with self.lock:
            created = self.conn.execute(
                "SELECT COUNT(*) AS n FROM signals WHERE created_at>=? AND created_at<?", (start, end)
            ).fetchone()["n"]
            tp = self.conn.execute(
                "SELECT COUNT(*) AS n FROM signals WHERE status='TP' AND closed_at>=? AND closed_at<?", (start, end)
            ).fetchone()["n"]
            cl = self.conn.execute(
                "SELECT COUNT(*) AS n FROM signals WHERE status='CL' AND closed_at>=? AND closed_at<?", (start, end)
            ).fetchone()["n"]
            expired = self.conn.execute(
                "SELECT COUNT(*) AS n FROM signals WHERE status IN ('EXPIRED','MISSED','INVALIDATED') AND closed_at>=? AND closed_at<?",
                (start, end),
            ).fetchone()["n"]
        return {"created": int(created), "tp": int(tp), "cl": int(cl), "expired": int(expired)}


STORE = SignalStore(path_of(DB_FILENAME))


# ============================================================================
# GENERAL HELPERS / API / RATE LIMIT GUARD
# ============================================================================

def safe_float(value: Any, default: float = 0.0) -> float:
    try:
        if value is None or value == "":
            return default
        if isinstance(value, str):
            value = value.replace(",", "")
        return float(value)
    except (TypeError, ValueError):
        return default


def safe_int(value: Any, default: int = 0) -> int:
    try:
        return int(safe_float(value, default))
    except (TypeError, ValueError):
        return default


def now_wib() -> datetime:
    return datetime.now(WIB)


def wait_if_rate_limited() -> None:
    now_ts = time.time()
    if now_ts < RATE_LIMIT_UNTIL:
        STOP_EVENT.wait(RATE_LIMIT_UNTIL - now_ts)


def cleanup_daily_memory(today_str: str, active_watchlist: List[str]) -> None:
    """Bersihkan riwayat memori & reset BLACKLIST_402 setiap pergantian hari."""
    keep = set(active_watchlist) | {s["symbol"] for s in STORE.active_signals()}
    with LOCK:
        BLACKLIST_402.clear()
        for sym in list(PRICE_HISTORY.keys()):
            if sym not in keep:
                del PRICE_HISTORY[sym]
        for sym, info in list(TICK_CACHE.items()):
            if info[0] != today_str and sym not in keep:
                del TICK_CACHE[sym]


def parse_api_timestamp(data: Dict[str, Any]) -> Optional[float]:
    candidates = [
        data.get("timestamp"), data.get("updated_at"), data.get("updatedAt"),
        data.get("datetime"), data.get("time"), data.get("last_update"),
    ]
    for value in candidates:
        if value is None or value == "":
            continue
        if isinstance(value, (int, float)):
            return float(value) / 1000.0 if float(value) > 1e12 else float(value)
        if isinstance(value, str):
            text = value.strip()
            try:
                numeric = float(text)
                return numeric / 1000.0 if numeric > 1e12 else numeric
            except ValueError:
                pass
            try:
                parsed = datetime.fromisoformat(text.replace("Z", "+00:00"))
                if parsed.tzinfo is None:
                    parsed = parsed.replace(tzinfo=WIB)
                return parsed.timestamp()
            except ValueError:
                continue
    return None


def response_is_fresh(data: Dict[str, Any]) -> bool:
    stamp = parse_api_timestamp(data)
    if stamp is None:
        return True
    age = time.time() - stamp
    return -30 <= age <= 120


def is_special_board(data: Dict[str, Any]) -> bool:
    values = [data.get("board"), data.get("market_board"), data.get("listing_board"), data.get("board_name")]
    text = " ".join(str(v) for v in values if v is not None).lower()
    return any(term in text for term in ("pemantauan khusus", "special monitoring", "periodic call", "papan khusus"))


def extract_lots(item: Dict[str, Any], volume_unit: str) -> int:
    if item.get("lot") is not None:
        return max(0, safe_int(item.get("lot")))
    raw = item.get("volume", item.get("qty", item.get("quantity", 0)))
    amount = max(0.0, safe_float(raw))
    if volume_unit.lower() == "shares":
        return int(amount // 100)
    return int(amount)


def get_previous_close(data: Dict[str, Any]) -> Optional[float]:
    for key in ("previous_close", "previousClose", "prev_close", "prevclose", "prev", "prevPrice", "previous"):
        value = safe_float(data.get(key))
        if value > 0:
            return value
    return None


def tick_size(price: float) -> int:
    if price < 200:
        return 1
    if price < 500:
        return 2
    if price < 2000:
        return 5
    if price < 5000:
        return 10
    return 25


def get_daily_tick(symbol: str, data: Dict[str, Any], last: float) -> int:
    today = now_wib().strftime("%Y-%m-%d")
    cached = TICK_CACHE.get(symbol)
    if cached and cached[0] == today:
        return cached[1]
    persisted = STORE.get_tick_ref(symbol, today)
    if persisted:
        ref_price, tick, source = persisted
        TICK_CACHE[symbol] = (today, tick, source)
        return tick
    prev_close = get_previous_close(data)
    if prev_close:
        ref_price = prev_close
        source = "previous_close_api"
    else:
        ref_price = last
        source = "first_last_fallback"
    tick = tick_size(ref_price)
    STORE.set_tick_ref(symbol, today, ref_price, tick, source)
    TICK_CACHE[symbol] = (today, tick, source)
    return tick


def add_ticks(price: float, ticks: int) -> int:
    """Menggeser harga mengikuti fraksi kelompok harga BEI yang valid di setiap langkah."""
    h = int(round(price))
    step_dir = 1 if ticks > 0 else -1
    for _ in range(abs(ticks)):
        if step_dir > 0:
            if h < 200:
                h += 1
            elif h < 500:
                h += 2
            elif h < 2000:
                h += 5
            elif h < 5000:
                h += 10
            else:
                h += 25
        else:
            if h <= 200:
                h -= 1
            elif h <= 500:
                h -= 2
            elif h <= 2000:
                h -= 5
            elif h <= 5000:
                h -= 10
            else:
                h -= 25
    return max(h, 1)


def get_daily_value(data: Dict[str, Any], last: int) -> float:
    value = safe_float(data.get("value"))
    if value > 0:
        return value
    volume = safe_float(data.get("volume"))
    if volume <= 0:
        return 0.0
    shares = volume if DAILY_VOLUME_UNIT.lower() == "shares" else volume * 100
    return last * shares


def http_get_json(url: str, label: str) -> Optional[Dict[str, Any]]:
    global RATE_LIMIT_UNTIL
    if AUTH_EXPIRED.is_set() or STOP_EVENT.is_set():
        return None
    wait_if_rate_limited()
    session = get_session()
    for attempt in range(HTTP_RETRIES + 1):
        if STOP_EVENT.is_set():
            return None
        try:
            response = session.get(url, timeout=REQUEST_TIMEOUT_SECONDS)
            if response.status_code == 200:
                try:
                    payload = response.json()
                    return payload if isinstance(payload, dict) else None
                except ValueError:
                    preview = response.text[:150].replace("\n", " ")
                    log(f"[{label}] Respons API bukan JSON valid (HTTP {response.status_code}): {preview}")
                    return None

            if response.status_code == 401:
                if not AUTH_EXPIRED.is_set():
                    AUTH_EXPIRED.set()
                    reply_cmd(ADMIN_ID or CHAT_ID,"⚠️ Bearer Token Stockbit Expired! Segera update token.txt dan restart bot.")
                log(f"[{label}] HTTP 401: Bearer Token Stockbit kedaluwarsa/tidak valid.")
                return None
            if response.status_code == 402:
                return {"__http_status__": 402}
            if response.status_code == 429:
                retry_after = safe_float(response.headers.get("Retry-After"), 0)
                pause = retry_after if retry_after > 0 else 20.0
                with LOCK:
                    RATE_LIMIT_UNTIL = max(RATE_LIMIT_UNTIL, time.time() + pause)
                log(f"[{label}] HTTP 429 rate limit; semua jalur jeda {pause:.0f} detik.")
                STOP_EVENT.wait(pause)
                continue
            if response.status_code >= 500 and attempt < HTTP_RETRIES:
                STOP_EVENT.wait(min(2 ** attempt, 8))
                continue
            log(f"[{label}] HTTP {response.status_code}: {response.text[:200]}")
            return None
        except requests.RequestException as exc:
            if attempt < HTTP_RETRIES:
                STOP_EVENT.wait(min(2 ** attempt, 8))
            else:
                log(f"[{label}] Koneksi gagal: {exc}")
    return None


def fetch_screener(url: str = "", label: str = "Screener") -> List[str]:
    target = url or SCREENER_URL
    if not target or "ISI_URL" in target:
        return []
    payload = http_get_json(target, label)
    if not payload or payload.get("__http_status__"):
        return []
    calcs = payload.get("data", {}).get("calcs", []) if isinstance(payload.get("data"), dict) else []
    if not isinstance(calcs, list):
        log(f"[{label}] Struktur payload screener tidak dikenali (calcs bukan list).")
        return []
    if not calcs:
        log(f"[{label}] Payload valid tapi calcs kosong (screener tidak mengembalikan saham).")
        return []
    try:
        calcs = sorted(
            calcs,
            key=lambda x: safe_float((x.get("results") or [{}])[-1].get("raw")),
            reverse=True,
        )
    except Exception:
        pass
    symbols = []
    for row in calcs:
        company = row.get("company") or {}
        symbol = str(company.get("symbol") or "").upper().strip()
        if re.fullmatch(r"[A-Z0-9]{4,6}", symbol) and symbol not in BLACKLIST_402 and symbol not in EXCLUDED_SYMBOLS:
            if symbol not in symbols:
                symbols.append(symbol)
    return symbols

def fetch_screener_with_fallback() -> List[str]:
    primary = fetch_screener(SCREENER_URL, "Screener#1")
    if primary:
        return primary
    if SCREENER_URL_2:
        log("Screener #1 kosong/gagal, mencoba Screener #2...")
        secondary = fetch_screener(SCREENER_URL_2, "Screener#2")
        if secondary:
            log(f"Screener #2 memberi {len(secondary)} saham.")
            return secondary
        log("Screener #2 juga kosong/gagal.")
    return []

def resolve_universe(screener_symbols: List[str]) -> List[str]:
    mode = MODE_CAKUPAN.strip().upper()
    if mode == "CUSTOM":
        return WATCHLIST_FALLBACK[:]
    if mode == "TOP_N":
        return screener_symbols[:MAX_SAHAM] if screener_symbols else WATCHLIST_FALLBACK[:MAX_SAHAM]
    return screener_symbols if screener_symbols else WATCHLIST_FALLBACK[:]


def fetch_orderbook(symbol: str) -> Optional[Dict[str, Any]]:
    if symbol in BLACKLIST_402 or symbol in EXCLUDED_SYMBOLS or AUTH_EXPIRED.is_set() or STOP_EVENT.is_set():
        return None
    url = f"https://exodus.stockbit.com/company-price-feed/v2/orderbook/companies/{symbol}"
    payload = http_get_json(url, symbol)
    if not payload:
        return None
    if payload.get("__http_status__") == 402:
        with LOCK:
            BLACKLIST_402.add(symbol)
        log(f"[{symbol}] HTTP 402 (kuota/akses terbatas); di-skip.")
        return None
    data = payload.get("data", {})
    return data if isinstance(data, dict) else None

def safe_get_field(data: Dict[str, Any], keys: tuple, default: Any = None) -> Any:
    """Mencari nilai dari beberapa alternatif key untuk mengantisipasi perubahan API."""
    for key in keys:
        if key in data and data[key] is not None:
            return data[key]
    return default


# ============================================================================
# JAM PERDAGANGAN BEI & BATAS WAKTU PRE-CLOSING
# ============================================================================

def in_regular_market_hours(now: datetime) -> Tuple[bool, str]:
    if not LIVE_MODE:
        return True, "MODE TES AKTIF (Bypass Jam Bursa)"
    if now.weekday() >= 5:
        return False, "Akhir pekan (Bursa libur)"
    if now.date() in HOLIDAYS:
        return False, "Libur bursa (hari_libur.txt)"

    clock = now.hour * 3600 + now.minute * 60 + now.second
    if now.weekday() == 4:
        sessions = ((9 * 3600 + 5 * 60, 11 * 3600 + 29 * 60 + 59), (14 * 3600, 15 * 3600 + 49 * 60 + 59))
    else:
        sessions = ((9 * 3600 + 5 * 60, 11 * 3600 + 59 * 60 + 59), (13 * 3600 + 30 * 60, 15 * 3600 + 49 * 60 + 59))

    for start, end in sessions:
        if start <= clock <= end:
            label = "Sesi I" if start == sessions[0][0] else "Sesi II"
            return True, f"{label} aktif"
    return False, "Standby (Di luar sesi Pasar Reguler)"


def effective_max_age(now: datetime) -> int:
    """Pangkas umur maksimal sinyal menjelang 15:50 WIB agar tidak menggantung masuk pre-closing."""
    if not LIVE_MODE:
        return MAX_SIGNAL_AGE_SECONDS
    pre_close = now.replace(hour=15, minute=49, second=50, microsecond=0)
    seconds_to_close = int((pre_close - now).total_seconds())
    if 0 < seconds_to_close < MAX_SIGNAL_AGE_SECONDS:
        return max(60, seconds_to_close)
    return MAX_SIGNAL_AGE_SECONDS


# ============================================================================
# TELEGRAM & REMOTE COMMAND LISTENER (/status, /pause, /resume, /pagi)
# ============================================================================

def telegram_ready() -> bool:
    return bool(TELEGRAM_TOKEN and CHAT_ID and "ISI_" not in TELEGRAM_TOKEN and "ISI_" not in CHAT_ID)


def telegram_request(method: str, payload: Dict[str, Any], timeout: int = 8) -> Optional[Any]:
    if not telegram_ready():
        return None
    url = f"https://api.telegram.org/bot{TELEGRAM_TOKEN}/{method}"
    for _ in range(3):
        if STOP_EVENT.is_set():
            return None
        try:
            response = requests.post(url, json=payload, timeout=timeout)
            result = response.json()
            if response.status_code == 200 and result.get("ok"):
                return result.get("result")
            if response.status_code in (400, 401, 403):
                break
        except (requests.RequestException, ValueError):
            time.sleep(2)
    return None

def send_telegram(message: str, topic_id: Optional[int] = None) -> Optional[int]:
    target_topic = TOPIC_ID if topic_id is None else topic_id
    payload: Dict[str, Any] = {
        "chat_id": CHAT_ID,
        "text": message,
        "disable_web_page_preview": True,
    }
    if target_topic > 0:
        payload["message_thread_id"] = target_topic
    result = telegram_request("sendMessage", payload)
    return safe_int(result.get("message_id")) if isinstance(result, dict) else None

def edit_telegram(message_id: Optional[int], message: str) -> None:
    if not message_id:
        return
    telegram_request("editMessageText", {"chat_id": CHAT_ID, "message_id": message_id, "text": message, "disable_web_page_preview": True})

def reply_cmd(target_id: str, msg_text: str) -> None:
    p = {"chat_id": target_id, "text": msg_text, "disable_web_page_preview": True}
    if target_id == str(CHAT_ID) and TOPIC_ID > 0:
        p["message_thread_id"] = TOPIC_ID
    telegram_request("sendMessage", p)

def analyze_quick_check(symbol: str) -> str:
    sym = symbol.upper().strip().replace("$", "")
    if not re.fullmatch(r"[A-Z0-9]{4,6}", sym):
        return "❌ Kode saham tidak valid. Contoh: /cek TRON"

    data = fetch_orderbook(sym)
    if not data:
        return f"⚠️ Data ${sym} gagal ditarik atau akses dibatasi."

    last = safe_int(safe_get_field(data, ("lastprice", "lastPrice", "last", "close")))
    high = safe_int(safe_get_field(data, ("high", "highPrice", "highest")))
    low = safe_int(safe_get_field(data, ("low", "lowPrice", "lowest")))
    avg_p = safe_float(safe_get_field(data, ("average", "vwap", "avgPrice")))
    prev = get_previous_close(data) or low
    bids = data.get("bid") if isinstance(data.get("bid"), list) else []
    offers = data.get("offer") if isinstance(data.get("offer"), list) else []

    if last <= 0 or not bids or not offers:
        return f"ℹ️ Orderbook ${sym} sedang kosong atau belum aktif."

    chg_pct = ((last - prev) / prev * 100.0) if prev > 0 else 0.0
    val_b = get_daily_value(data, last) / 1_000_000_000
    tick = tick_size(last)
    bid1_p = safe_int(bids[0].get("price"))
    offer1_p = safe_int(offers[0].get("price"))
    bid1_lot = extract_lots(bids[0], ORDERBOOK_VOLUME_UNIT)
    offer1_lot = extract_lots(offers[0], ORDERBOOK_VOLUME_UNIT)
    bid_top2 = sum(extract_lots(x, ORDERBOOK_VOLUME_UNIT) for x in bids[:2])
    offer_top2 = sum(extract_lots(x, ORDERBOOK_VOLUME_UNIT) for x in offers[:2])
    spread_ok = (offer1_p - bid1_p) <= tick and offer1_p > bid1_p

    # Cek kondisi IHSG (COMPOSITE)
    ihsg_pct = 0.0
    ihsg_note = ""
    ihsg_data = fetch_orderbook("COMPOSITE")
    if ihsg_data:
        i_last = safe_float(safe_get_field(ihsg_data, ("lastprice", "lastPrice", "last", "close")))
        i_prev = get_previous_close(ihsg_data) or i_last
        if i_last > 0 and i_prev > 0:
            ihsg_pct = ((i_last - i_prev) / i_prev) * 100.0
            if ihsg_pct <= -0.5:
                ihsg_note = f" Namun IHSG sedang melemah ({ihsg_pct:+.2f}%), tetap hati-hati dan batasi lot."
            elif ihsg_pct >= 0.3:
                ihsg_note = f" IHSG juga menguat ({ihsg_pct:+.2f}%), peluang lanjut naik masih terbuka."

    above_avg = (last >= int(avg_p)) if avg_p > 0 else True
    wall_p, wall_lot = 0, 0
    for lvl in offers[:3]:
        lp = safe_int(lvl.get("price"))
        ll = extract_lots(lvl, ORDERBOOK_VOLUME_UNIT)
        if ll >= MIN_WALL_LOT:
            wall_p, wall_lot = lp, ll
            break

    # Rakit kalimat info dinamis tanpa istilah indikator
    alasan = []
    if val_b >= 10.0:
        alasan.append("Transaksi sangat ramai")
    elif val_b >= 2.0:
        alasan.append("Transaksi cukup likuid")
    else:
        alasan.append("Transaksi masih sepi")

    alasan.append("dengan spread rapat (1 tick)." if spread_ok else "dan spread renggang sehingga rawan susah keluar.")

    if bid_top2 > offer_top2 and above_avg:
        alasan.append("Pembeli dominan menjaga antrean bawah dan harga bertahan kuat di area atas.")
    elif not above_avg:
        alasan.append("Tekanan jual lebih besar dan harga masih tertekan di area bawah.")
    elif wall_p > 0:
        alasan.append(f"Ada tembok jual tebal di {wall_p} ({wall_lot:,} lot) yang perlu ditembus.")
    else:
        alasan.append("Pergerakan harga masih seimbang menunggu dorongan antrean baru.")

    info_text = " ".join(alasan) + ihsg_note

    # Penentuan status & harga rencana entry
    is_good = above_avg and spread_ok and val_b >= 2.0 and not is_special_board(data)
    if is_good:
        status_hdr = "⚠️ SIAP PANTAU (HATI-HATI IHSG MERAH)" if ihsg_pct <= -0.5 else "🟢 AMAN / SIAP ENTRY"
        bo_entry = add_ticks(wall_p if wall_p > 0 else max(offer1_p, high), 1)
        bo_tp = add_ticks(bo_entry, 4)
        bo_cl = add_ticks(bo_entry, -3)

        pb_base = int(round(avg_p)) if avg_p > 0 else add_ticks(last, -2)
        pb_1 = min(add_ticks(last, -1), add_ticks(pb_base, 1))
        pb_2 = add_ticks(pb_1, -1)
        pb_tp = add_ticks(pb_1, 4)
        pb_cl = add_ticks(pb_2, -2)

        aksi_lines = (
            f"• Masuk Cepat: Tunggu jebol {bo_entry} (TP {bo_tp} | CL {bo_cl})\n"
            f"• Antre Bawah: {pb_2} – {pb_1} (TP {pb_tp} | CL {pb_cl})"
        )
    else:
        status_hdr = "⛔ JANGAN MASUK"
        reclaim = max(int(round(avg_p)) if avg_p > 0 else add_ticks(last, 2), add_ticks(offer1_p, 1))
        supp = add_ticks(low, -1) if low > 0 else add_ticks(last, -3)
        aksi_lines = f"• Pantau: Tunggu kuat di atas {reclaim} atau area {supp}"

    return (
        f"📊 ${sym} — {last} ({chg_pct:+.2f}%)\n"
        f"Val: Rp {val_b:.1f} M | Bid: {bid1_p} ({bid1_lot:,}) | Offer: {offer1_p} ({offer1_lot:,})\n\n"
        f"{status_hdr}\n"
        f"{aksi_lines}\n"
        f"• Info: {info_text}"
    )
    
def send_test_showcase(target_id: str) -> None:
    """Mengirim diagnostik parameter & semua contoh tampilan indikator sinyal ke Telegram."""
    mode_str = "LIVE" if LIVE_MODE else "TEST"
    token_ok = "✅ OK" if (BEARER_TOKEN and not AUTH_EXPIRED.is_set()) else "❌ EXPIRED/KOSONG"
    wl_count = len(CURRENT_WATCHLIST_SHARED)

    diagnostik = (
        f"🧪 UJI COBA INDIKATOR SEDAYU BOT ({mode_str})\n"
        f"• Token Stockbit: {token_ok} | Watchlist: {wl_count} saham\n"
        f"• Worker: {JUMLAH_WORKER} | Slow: {SCAN_INTERVAL_SECONDS}s | Fast: {FAST_LANE_INTERVAL_SECONDS}s\n"
        f"• Min Wall: {MIN_WALL_LOT:,} lot | Bid Support: {MIN_BID_SUPPORT_LOT:,} lot\n"
        f"• PB Range: ≥{MIN_PULLBACK_RANGE_PERCENT}% | Jarak VWAP: ≤{MAX_PULLBACK_VWAP_DISTANCE_PERCENT}%\n"
        f"• Peringatan Pucuk: ≥+{MAX_GAIN_WARNING_PERCENT:.0f}% | Max Aktif: {MAX_ACTIVE_SIGNALS} sinyal"
    )
    reply_cmd(target_id, diagnostik)
    time.sleep(0.4)

    # 1. Contoh Sinyal Breakout (WAITING)
    sample_bo_wait = {
        "symbol": "PTRO",
        "kind": "BO",
        "status": "WAIT_BREAKOUT",
        "last_at_alert": 2540,
        "current_last": 2540,
        "entry": 2550,
        "tp": 2590,
        "cl": 2520,
        "gain_pct": 6.5,
    }
    reply_cmd(target_id, signal_message(sample_bo_wait))
    time.sleep(0.4)

    # 2. Contoh Sinyal Breakout (ACTIVE + Rawan Pucuk)
    sample_bo_active = {
        "symbol": "RAJA",
        "kind": "BO",
        "status": "ACTIVE",
        "last_at_alert": 1820,
        "current_last": 1825,
        "entry": 1825,
        "tp": 1845,
        "cl": 1810,
        "gain_pct": 16.4,
    }
    reply_cmd(target_id, signal_message(sample_bo_active))
    time.sleep(0.4)

    # 3. Contoh Sinyal Pullback (WAITING)
    sample_pb_wait = {
        "symbol": "MEDC",
        "kind": "PB",
        "status": "WAIT_ENTRY",
        "last_at_alert": 1230,
        "current_last": 1230,
        "p1": 1225,
        "p2": 1220,
        "p3": 1215,
        "tp": 1245,
        "cl": 1205,
        "gain_pct": 4.2,
    }
    reply_cmd(target_id, signal_message(sample_pb_wait))
    time.sleep(0.4)

    # 4. Contoh Hasil Sinyal Selesai (TP)
    hasil_tp = (
        "✅ $PTRO BO (TP)\n"
        "2550 | Last 2590\n"
        "TP 2590 | CL 2520"
    )
    reply_cmd(target_id, hasil_tp)

def telegram_command_loop() -> None:
    """Mendengarkan perintah dari chat Telegram pemilik bot secara ringan (long-polling)."""
    if not telegram_ready():
        return
    offset = 0
    initial = telegram_request("getUpdates", {"timeout": 1}, timeout=5)
    if isinstance(initial, list) and initial:
        offset = initial[-1].get("update_id", 0) + 1

    while not STOP_EVENT.is_set():
        updates = telegram_request("getUpdates", {"offset": offset, "timeout": 15}, timeout=20)
        if not isinstance(updates, list):
            STOP_EVENT.wait(3)
            continue

        for upd in updates:
            offset = max(offset, upd.get("update_id", 0) + 1)
            msg = upd.get("message") or {}
            chat_id = str((msg.get("chat") or {}).get("id") or "")
            sender_id = str((msg.get("from") or {}).get("id") or "")

            # Wajib cocok dengan User ID pribadi kamu (member lain otomatis diabaikan)
            if not ADMIN_ID or sender_id != str(ADMIN_ID):
                continue

            # Hanya terima perintah dari grup utama atau chat pribadi (japri) kamu ke bot
            if chat_id not in {str(CHAT_ID), str(ADMIN_ID)}:
                continue

            text = str(msg.get("text") or "").strip().lower()
            if text in ("/status", "status"):
                now = now_wib()
                _, m_status = in_regular_market_hours(now)
                aktif = STORE.active_signals()
                daftar_aktif = ", ".join(f"${s['symbol']}({s['kind']})" for s in aktif) if aktif else "Kosong"
                kondisi_scan = "⏸️ PAUSED" if SCAN_PAUSED.is_set() else ("⚠️ TOKEN EXPIRED" if AUTH_EXPIRED.is_set() else "🟢 AKTIF")
                reply_cmd(chat_id,
                    f"🤖 SEDAYU SCALPING STATUS ({'LIVE' if LIVE_MODE else 'TEST'})\n"
                    f"• Radar: {kondisi_scan}\n"
                    f"• Bursa: {m_status}\n"
                    f"• Watchlist: {len(CURRENT_WATCHLIST_SHARED)} saham ({JUMLAH_WORKER} worker)\n"
                    f"• Sinyal Aktif ({len(aktif)}/{MAX_ACTIVE_SIGNALS}): {daftar_aktif}"
                )
            elif text in ("/pause", "pause"):
                SCAN_PAUSED.set()
                reply_cmd(chat_id, "⏸️ Pencarian sinyal baru dijeda (/pause). Sinyal yang sudah aktif tetap dipantau sampai TP/CL.")
                log("Bot dijeda oleh user via Telegram (/pause).")
            elif text in ("/resume", "resume"):
                SCAN_PAUSED.clear()
                reply_cmd(chat_id, "▶️ Pencarian sinyal baru dilanjutkan (/resume).")
                log("Bot dilanjutkan oleh user via Telegram (/resume).")
            elif text in ("/pagi", "pagi"):
                reply_cmd(chat_id, "🔍 Memindai kandidat Scalping Watchlist...")
                with LOCK:
                    wl = CURRENT_WATCHLIST_SHARED[:]
                send_morning_watchlist(now_wib(), wl, force=True)
            elif text in ("/rekap", "rekap"):
                reply_cmd(chat_id, "📊 Mengirim tes Rekap Harian ke topik Winrate...")
                send_daily_report(now_wib())
            elif text in ("/tes", "tes"):
                send_test_showcase(chat_id)
            elif text.startswith("/cek "):
                raw_text = str(msg.get("text") or "").strip()
                parts = raw_text.split(None, 1)
                if len(parts) > 1:
                    kode = parts[1].strip()
                    reply_cmd(chat_id, f"🔍 Mengecek kondisi ${kode.upper()} & IHSG...")
                    hasil_cek = analyze_quick_check(kode)
                    reply_cmd(chat_id, hasil_cek)
                else:
                    reply_cmd(chat_id, "❌ Ketik kode sahamnya. Contoh: /cek TRON")

            elif text.startswith("/token "):
                raw_text = str(msg.get("text") or "").strip()
                new_tok = raw_text.split(None, 1)[1].strip()
                if new_tok.lower().startswith("bearer "):
                    new_tok = new_tok[7:].strip()
                if len(new_tok) > 20:
                    with LOCK:
                        HEADERS["Authorization"] = f"Bearer {new_tok}"
                        AUTH_EXPIRED.clear()
                        BLACKLIST_402.clear()
                    try:
                        with open(path_of("token.txt"), "w", encoding="utf-8") as f:
                            f.write(new_tok + "\n")
                    except Exception:
                        pass
                    reply_cmd(chat_id, "✅ Bearer Token Stockbit berhasil diperbarui! Radar kembali aktif.")
                    log("Bearer Token diperbarui via perintah Telegram /token.")
                else:
                    reply_cmd(chat_id, "❌ Format token tidak valid. Ketik: /token <paste_token_baru>")



# ============================================================================
# FORMAT PESAN & STATE MACHINE
# ============================================================================

def mode_prefix() -> str:
    return "" if LIVE_MODE else ""


def signal_message(state: Dict[str, Any]) -> str:
    status = state.get("status", "")
    ikon = "🚀" if status == "ACTIVE" else "⏳"
    harga_skrg = state.get("current_last", state["last_at_alert"])
    gain_pct = safe_float(state.get("gain_pct"), 0.0)
    pucuk_tag = f" ⚠️ (+{gain_pct:.1f}% Rawan Pucuk)" if gain_pct >= MAX_GAIN_WARNING_PERCENT else ""

    tp = int(state["tp"])
    cl = int(state["cl"])

    if state["kind"] == "BO":
        entry = int(state["entry"])
        tp_pct = ((tp * 0.9975) - (entry * 1.0015)) / (entry * 1.0015) * 100.0 if entry > 0 else 0.0
        cl_pct = ((cl * 0.9975) - (entry * 1.0015)) / (entry * 1.0015) * 100.0 if entry > 0 else 0.0
        return (
            f"${state['symbol']} BO {harga_skrg} {ikon}{pucuk_tag}\n"
            f"{entry}\n"
            f"TP {tp} ({tp_pct:+.1f}%)\n"
            f"CL {cl} ({cl_pct:+.1f}%)"
        )

    p1 = int(state["p1"])
    tp_pct = ((tp * 0.9975) - (p1 * 1.0015)) / (p1 * 1.0015) * 100.0 if p1 > 0 else 0.0
    cl_pct = ((cl * 0.9975) - (p1 * 1.0015)) / (p1 * 1.0015) * 100.0 if p1 > 0 else 0.0
    return (
        f"${state['symbol']} PULLBACK {harga_skrg} {ikon}{pucuk_tag}\n"
        f"{p1} | {state['p2']} | {state['p3']}\n"
        f"TP {tp} ({tp_pct:+.1f}%)\n"
        f"CL {cl} ({cl_pct:+.1f}%)"
    )


def create_signal(state: Dict[str, Any]) -> None:
    if SCAN_PAUSED.is_set():
        return
    with LOCK:
        if STORE.active_count() >= MAX_ACTIVE_SIGNALS:
            return
        if STORE.has_active(state["symbol"], state["kind"]) or STORE.has_recent_key(state["signal_key"], COOLDOWN_SECONDS):
            return
        STORE.save_signal(state)
        STORE.event(state["signal_id"], "CREATED", state.get("display_status", ""))

    message_id = send_telegram(signal_message(state))
    if message_id:
        with LOCK:
            state["message_id"] = message_id
            STORE.save_signal(state)
    log(f"[{state['symbol']}] {state['kind']} {state.get('display_status')} | TP {state['tp']} | CL {state['cl']}")


def finalize_signal(state: Dict[str, Any], final_status: str, last: int) -> None:
    with LOCK:
        state["last_at_close"] = last
        note = f"last={last}; TP={state.get('tp')}; CL={state.get('cl')}"
        STORE.close_signal(state, final_status, note)

    tag = mode_prefix()
    if final_status == "TP":
        ikon = "✅"
    elif final_status in ("EXPIRED", "MISSED"):
        ikon = "⛔"
    else:
        ikon = "❌"

    label_status = "GAGAL" if final_status == "INVALIDATED" else final_status
    entry_ref = state.get("entry") if state["kind"] == "BO" else f"{state['p1']} | {state['p2']} | {state['p3']}"
    message = (
        f"{ikon} {tag}${state['symbol']} {state['kind']} ({label_status})\n"
        f"{entry_ref} | Last {last}\n"
        f"TP {state['tp']} | CL {state['cl']}"
    )
    edit_telegram(state.get("message_id"), message)
    log(f"[HASIL] {state['symbol']} {state['kind']} -> {final_status} (last {last})")


def monitor_active_signals(symbol: str, last: int) -> None:
    now_ts = time.time()
    max_age = effective_max_age(now_wib())

    for state in STORE.active_signals(symbol):
        age = now_ts - float(state.get("created_at", now_ts))
        kind = state.get("kind")
        status = state.get("status")

        if kind == "BO" and status == "WAIT_BREAKOUT":
            entry = int(state["entry"])
            cl = int(state["cl"])
            if last <= cl:
                finalize_signal(state, "INVALIDATED", last)
            elif last >= entry:
                with LOCK:
                    state["status"] = "ACTIVE"
                    state["entry_confirmed"] = True
                    state["entry_touch_at"] = now_ts
                    state["current_last"] = last
                    state["display_status"] = "BREAKOUT CONFIRMED"
                    STORE.save_signal(state)
                    STORE.event(state["signal_id"], "BREAKOUT_CONFIRMED", f"last={last}")
                edit_telegram(state.get("message_id"), signal_message(state))
                log(f"[{symbol}] BO terkonfirmasi jebol pada last {last} (>= entry {entry})")
            elif age >= max_age:
                finalize_signal(state, "EXPIRED", last)
            continue

        if kind == "BO" and status == "ACTIVE":
            entry = int(state["entry"])
            tp = int(state["tp"])
            bep_trigger = add_ticks(entry, 2)
            if last >= tp:
                finalize_signal(state, "TP", last)
            elif last <= int(state["cl"]):
                finalize_signal(state, "CL", last)
            elif last >= bep_trigger and int(state["cl"]) < entry:
                with LOCK:
                    state["cl"] = entry
                    state["current_last"] = last
                    STORE.save_signal(state)
                    STORE.event(state["signal_id"], "TRAILING_BEP", f"last={last}; new_cl={entry}")
                edit_telegram(state.get("message_id"), signal_message(state))
                log(f"[{symbol}] BO Auto-Trailing: CL digeser ke BEP {entry} (last {last})")
            elif age >= max_age:
                finalize_signal(state, "EXPIRED", last)
            continue


        if kind == "PB" and status == "WAIT_ENTRY":
            p1 = int(state["p1"])
            cl = int(state["cl"])
            tp = int(state["tp"])
            if last <= cl:
                finalize_signal(state, "INVALIDATED", last)
            elif last <= p1:
                with LOCK:
                    state["status"] = "ACTIVE"
                    state["entry_confirmed"] = True
                    state["entry_touch_at"] = now_ts
                    state["current_last"] = last
                    state["display_status"] = "AREA TOUCHED"
                    STORE.save_signal(state)
                    STORE.event(state["signal_id"], "AREA_TOUCHED", f"last={last}")
                edit_telegram(state.get("message_id"), signal_message(state))
                log(f"[{symbol}] PB area tersentuh pada last {last}")
            elif last >= tp:
                finalize_signal(state, "MISSED", last)
            elif age >= max_age:
                finalize_signal(state, "EXPIRED", last)
            continue

        if kind == "PB" and status == "ACTIVE":
            p1 = int(state["p1"])
            tp = int(state["tp"])
            bep_trigger = add_ticks(p1, 2)
            if last >= tp:
                finalize_signal(state, "TP", last)
            elif last <= int(state["cl"]):
                finalize_signal(state, "CL", last)
            elif last >= bep_trigger and int(state["cl"]) < p1:
                with LOCK:
                    state["cl"] = p1
                    state["current_last"] = last
                    STORE.save_signal(state)
                    STORE.event(state["signal_id"], "TRAILING_BEP", f"last={last}; new_cl={p1}")
                edit_telegram(state.get("message_id"), signal_message(state))
                log(f"[{symbol}] PB Auto-Trailing: CL digeser ke BEP {p1} (last {last})")
            elif age >= max_age:
                finalize_signal(state, "EXPIRED", last)



# ============================================================================
# STRATEGI BREAKOUT & PULLBACK (SPREAD GUARD + VWAP SUPPORT)
# ============================================================================

def is_spread_tight(bids: List[Dict[str, Any]], offers: List[Dict[str, Any]], tick: int) -> bool:
    if not bids or not offers or tick <= 0:
        return False
    bid1_price = safe_int(bids[0].get("price"))
    offer1_price = safe_int(offers[0].get("price"))
    if bid1_price <= 0 or offer1_price <= 0:
        return False
    return (offer1_price - bid1_price) <= tick


def detect_breakout(symbol: str, last: int, high: int, tick: int, value_billion: float,
                    offers: List[Dict[str, Any]], bids: List[Dict[str, Any]], gain_pct: float = 0.0) -> None:
    if SCAN_PAUSED.is_set() or STORE.active_count() >= MAX_ACTIVE_SIGNALS or STORE.has_active(symbol, "BO"):
        return
    if not is_spread_tight(bids, offers, tick):
        return

    bid_lots = sum(extract_lots(x, ORDERBOOK_VOLUME_UNIT) for x in bids[:2])
    if bid_lots < MIN_BID_SUPPORT_LOT:
        return

    kandidat = None
    for level in offers[:4]:
        wall_price = safe_int(level.get("price"))
        lots = extract_lots(level, ORDERBOOK_VOLUME_UNIT)
        if wall_price <= last or lots < MIN_WALL_LOT:
            continue

        if bid_lots < int(lots * MIN_BID_TO_WALL_RATIO):
            continue

        distance_ticks = (wall_price - last) / tick if tick else 999
        near_high = wall_price >= high - (2 * tick)
        if distance_ticks == 1 and near_high:
            signal_key = f"{symbol}|BO|{wall_price}"
            if STORE.has_recent_key(signal_key, COOLDOWN_SECONDS):
                return
            kandidat = (wall_price, lots, signal_key)
            break

    if not kandidat:
        return

    wall_price, initial_lots, signal_key = kandidat
    wall_swept = False

    if LIVE_MODE:
        STOP_EVENT.wait(2.0)
        if STOP_EVENT.is_set():
            return
        recheck_data = fetch_orderbook(symbol)
        if not recheck_data:
            return

        new_last = safe_int(safe_get_field(recheck_data, ("lastprice", "lastPrice", "last", "close")))
        new_offers = recheck_data.get("offer") if isinstance(recheck_data.get("offer"), list) else []
        new_bids = recheck_data.get("bid") if isinstance(recheck_data.get("bid"), list) else []
        new_bid_lots = sum(extract_lots(x, ORDERBOOK_VOLUME_UNIT) for x in new_bids[:2])

        remaining_wall_lots = 0
        for lvl in new_offers[:5]:
            if safe_int(lvl.get("price")) == wall_price:
                remaining_wall_lots = extract_lots(lvl, ORDERBOOK_VOLUME_UNIT)
                break

        entry = add_ticks(wall_price, 1)
        already_broke = new_last >= entry
        wall_swept = (new_last >= wall_price and remaining_wall_lots == 0 and new_bid_lots >= MIN_BID_SUPPORT_LOT)
        wall_still_valid = remaining_wall_lots >= int(initial_lots * 0.5) and new_bid_lots >= MIN_BID_SUPPORT_LOT
        wall_eaten_up = new_last >= wall_price and remaining_wall_lots < initial_lots

        if not (already_broke or wall_swept or wall_still_valid or wall_eaten_up):
            log(f"[{symbol}] Spoof wall di {wall_price} terdeteksi, diabaikan.")
            return

        last = new_last
        initial_lots = max(initial_lots, remaining_wall_lots)

    now_ts = time.time()
    entry = add_ticks(wall_price, 1)
    tp = add_ticks(entry, 4)
    cl = add_ticks(wall_price, -2)
    signal_id = str(uuid.uuid4())

    is_confirmed = (last >= entry) or wall_swept
    state = {
        "signal_id": signal_id,
        "signal_key": signal_key,
        "symbol": symbol,
        "kind": "BO",
        "status": "ACTIVE" if is_confirmed else "WAIT_BREAKOUT",
        "display_status": "BREAKOUT CONFIRMED" if is_confirmed else "PREPARE / WAIT WALL",
        "created_at": now_ts,
        "message_id": None,
        "resistance": wall_price,
        "entry": entry,
        "tp": tp,
        "cl": cl,
        "last_at_alert": last,
        "current_last": last,
        "value_billion": value_billion,
        "wall_max_lots": initial_lots,
        "gain_pct": gain_pct,
        "entry_confirmed": is_confirmed,
    }
    create_signal(state)



def detect_pullback(symbol: str, last: int, high: int, low: int, vwap: float, tick: int,
                    value_billion: float, bids: List[Dict[str, Any]], offers: List[Dict[str, Any]],
                    gain_pct: float = 0.0) -> None:

    if low <= 0 or vwap <= 0 or high <= low or last <= 0:
        return

    if SCAN_PAUSED.is_set() or STORE.active_count() >= MAX_ACTIVE_SIGNALS or STORE.has_active(symbol, "PB"):
        return

    # Filter spread
    if not is_spread_tight(bids, offers, tick):
        return

    # Catat histori harga
    with LOCK:
        price_history = PRICE_HISTORY[symbol]
        now_ts = time.time()
        price_history.append((now_ts, last))

        samples = [
            item[1] for item in price_history
            if now_ts - item[0] <= 600
        ][-36:]

    # Minimal histori untuk membaca struktur harga
    if len(samples) < 8:
        return

    # =====================================================
    # 1. FILTER KONDISI HARGA DAN VWAP
    # =====================================================

    range_percent = ((high - low) / low) * 100.0
    vwap_distance = ((last - vwap) / vwap) * 100.0

    # Hindari saham terlalu sepi atau terlalu jauh dari VWAP
    if range_percent < 1.5:
        return

    if not (-0.5 <= vwap_distance <= MAX_VWAP_DISTANCE_ENTRY_PERCENT):
        return

    # =====================================================
    # 2. IDENTIFIKASI IMPULS NAIK
    # =====================================================

    peak_index = max(range(len(samples) - 3), key=lambda i: samples[i])
    peak_price = samples[peak_index]

    # Puncak harus terbentuk setelah awal histori
    if peak_index < 2:
        return

    base_price = min(samples[:peak_index + 1])

    if base_price <= 0 or peak_price <= base_price:
        return

    impulse_percent = ((peak_price - base_price) / base_price) * 100.0

    # Minimal impuls kenaikan 0,8%
    if impulse_percent < 0.8:
        return

    # =====================================================
    # 3. IDENTIFIKASI RETRACEMENT
    # =====================================================

    after_peak = samples[peak_index + 1:-1]

    if len(after_peak) < 2:
        return

    pullback_low = min(after_peak)

    if pullback_low <= 0 or pullback_low >= peak_price:
        return

    # Struktur koreksi tidak boleh merusak titik awal impuls
    if pullback_low <= base_price:
        return

    pullback_depth = peak_price - pullback_low

    retracement_percent = (
        pullback_depth / (peak_price - base_price)
    ) * 100.0

    # Koreksi sehat: 20%-65% dari impuls
    if not (20.0 <= retracement_percent <= 65.0):
        return

    # =====================================================
    # 4. KONFIRMASI PANTULAN
    # =====================================================

    previous_price = samples[-2]

    if last <= pullback_low:
        return

    if last <= previous_price:
        return

    bounce_percent = (
        (last - pullback_low) / pullback_depth
    ) * 100.0

    # Pantulan minimal 25%, maksimal 70%
    if not (25.0 <= bounce_percent <= 70.0):
        return

    # Jangan mengejar harga yang sudah terlalu dekat pucuk
    if last >= peak_price:
        return

    # =====================================================
    # 5. KONFIRMASI ORDERBOOK
    # =====================================================

    bid1 = extract_lots(bids[0], ORDERBOOK_VOLUME_UNIT)
    bid2 = extract_lots(bids[1], ORDERBOOK_VOLUME_UNIT) if len(bids) > 1 else 0

    offer1 = extract_lots(offers[0], ORDERBOOK_VOLUME_UNIT)

    bid_top3 = sum(
        extract_lots(x, ORDERBOOK_VOLUME_UNIT) for x in bids[:3]
    )

    offer_top3 = sum(
        extract_lots(x, ORDERBOOK_VOLUME_UNIT) for x in offers[:3]
    )

    if bid1 <= offer1:
        return

    if bid1 + bid2 < MIN_BID_SUPPORT_LOT:
        return

    if bid_top3 < offer_top3 * 1.20:
        return

    # =====================================================
    # 6. PENENTUAN ENTRY, TP DAN CL
    # =====================================================

    tick = tick_size(last)
    vwap_price = int(round(vwap / tick)) * tick

    # 1. Tentukan Support (Titik Terendah Pantulan)
    if vwap_price >= (last - (5 * tick)) and vwap_price < last:
        support = vwap_price
    else:
        support = int(round(pullback_low / tick)) * tick

    # 2. Hitung Jarak dalam Satuan TICK (BUKAN Rupiah)
    gap_rupiah = last - support
    if gap_rupiah < (2 * tick):
        return  # Terlalu mepet, skip aja, gak worth it

    gap_ticks = int(round(gap_rupiah / tick))

    # P1: Antrean pertama / tertinggi (2/3 dari support ke last)
    # P2: Antrean kedua / tengah (1/3 dari support ke last)
    # P3: Antrean ketiga / terbawah (Support)
    p1 = add_ticks(support, int(gap_ticks * 2 / 3))
    p2 = add_ticks(support, int(gap_ticks / 3))
    p3 = support

    # 3. Validasi: Urutan harga wajib Last > P1 > P2 > P3
    if p1 >= last:
        p1 = add_ticks(last, -1)
    if p2 >= p1:
        p2 = add_ticks(p1, -1)
    if p3 >= p2:
        p3 = add_ticks(p2, -1)

    # 4. Hitung TP & CL (100% Fraksi BEI Valid)
    tp = add_ticks(p1, 4)
    cl = add_ticks(p3, -1)

    # 5. Validasi Akhir
    if p3 <= 0 or cl <= 0 or last <= p1:
        return
    # =====================================================
    # 7. COOLDOWN DAN PEMBUATAN SINYAL
    # =====================================================

    signal_key = f"{symbol}|PB|{p1}"

    if STORE.has_recent_key(signal_key, COOLDOWN_SECONDS):
        return

    signal_id = str(uuid.uuid4())

    state = {
        "signal_id": signal_id,
        "signal_key": signal_key,
        "symbol": symbol,
        "kind": "PB",
        "status": "WAIT_ENTRY",
        "display_status": "SETUP / WAIT AREA",
        "created_at": now_ts,
        "message_id": None,

        "p1": p1,
        "p2": p2,
        "p3": p3,

        "tp": tp,
        "cl": cl,

        "last_at_alert": last,
        "current_last": last,

        "vwap": vwap,
        "value_billion": value_billion,

        "range_percent": range_percent,
        "vwap_distance_percent": vwap_distance,

        "impulse_percent": impulse_percent,
        "retracement_percent": retracement_percent,
        "bounce_percent": bounce_percent,

        "gain_pct": gain_pct,
        "entry_confirmed": False,
    }

    create_signal(state)



def analyze_symbol(symbol: str, data: Dict[str, Any], monitor_only: bool = False) -> None:
    try:
        if not response_is_fresh(data) or is_special_board(data):
            return

        raw_last = safe_get_field(data, ("lastprice", "lastPrice", "last", "close"))
        raw_high = safe_get_field(data, ("high", "highPrice", "highest"))
        raw_low = safe_get_field(data, ("low", "lowPrice", "lowest"))
        raw_vwap = safe_get_field(data, ("average", "vwap", "avgPrice"))
        raw_bids = safe_get_field(data, ("bid", "bids"))
        raw_offers = safe_get_field(data, ("offer", "offers", "ask", "asks"))

        last = safe_int(raw_last)
        high = safe_int(raw_high)
        low = safe_int(raw_low)
        vwap = safe_float(raw_vwap)
        bids = raw_bids if isinstance(raw_bids, list) else []
        offers = raw_offers if isinstance(raw_offers, list) else []

        if last <= 0 or high <= 0 or low <= 0 or not bids or not offers:
            return

        monitor_active_signals(symbol, last)
        if monitor_only or SCAN_PAUSED.is_set():
            return

        daily_value = get_daily_value(data, last)
        if daily_value < MIN_DAILY_VALUE_IDR:
            return
        tick = tick_size(last)
        value_billion = daily_value / 1_000_000_000
        prev_close = get_previous_close(data) or low
        gain_pct = ((last - prev_close) / prev_close * 100.0) if prev_close > 0 else 0.0

        detect_breakout(symbol, last, high, tick, value_billion, offers, bids, gain_pct)
        detect_pullback(symbol, last, high, low, vwap, tick, value_billion, bids, offers, gain_pct)
    except Exception as exc:
        log(f"[Error Analisa {symbol}] {type(exc).__name__}: {exc}")


def process_symbol(symbol: str, monitor_only: bool = False) -> None:
    if STOP_EVENT.is_set() or AUTH_EXPIRED.is_set():
        return
    STOP_EVENT.wait(random.uniform(0.05, 0.25))
    data = fetch_orderbook(symbol)
    if not data:
        return
    analyze_symbol(symbol, data, monitor_only=monitor_only)

# ============================================================================
# FAST-LANE PARALEL
# ============================================================================

def fast_lane_loop() -> None:
    with ThreadPoolExecutor(max_workers=MAX_ACTIVE_SIGNALS) as fast_executor:
        while not STOP_EVENT.is_set():
            if AUTH_EXPIRED.is_set():
                STOP_EVENT.wait(5)
                continue

            market_open, _ = in_regular_market_hours(now_wib())
            if not market_open:
                STOP_EVENT.wait(5)
                continue

            active_syms = list({s["symbol"] for s in STORE.active_signals()})
            if not active_syms:
                STOP_EVENT.wait(FAST_LANE_INTERVAL_SECONDS)
                continue

            futures = [fast_executor.submit(process_symbol, sym, True) for sym in active_syms]
            for fut in as_completed(futures):
                if STOP_EVENT.is_set():
                    break
                try:
                    fut.result()
                except Exception as exc:
                    log(f"[Fast-Lane Error] {type(exc).__name__}: {exc}")

            STOP_EVENT.wait(FAST_LANE_INTERVAL_SECONDS)

PREMARKET_CHECKED_DATE = ""

def check_premarket_token(now: datetime) -> None:
    global PREMARKET_CHECKED_DATE
    today_str = now.date().isoformat()
    if PREMARKET_CHECKED_DATE == today_str:
        return
    if now.weekday() >= 5 or now.date() in HOLIDAYS:
        return
    if not (now.hour == 8 and 45 <= now.minute <= 55):
        return

    PREMARKET_CHECKED_DATE = today_str
    data = fetch_orderbook("BBCA")
    if data and not AUTH_EXPIRED.is_set():
        reply_cmd(ADMIN_ID or CHAT_ID, "🟢 Pre-Market Check (08:45 WIB): Bearer Token Stockbit AKTIF, bot siap pantau pembukaan bursa!")
        log("Pre-market token check: OK.")
    elif not AUTH_EXPIRED.is_set():
        reply_cmd(ADMIN_ID or CHAT_ID, "⚠️ Pre-Market Check (08:45 WIB): Gagal terhubung ke API Stockbit, cek status token kamu.")

# ============================================================================
# MORNING SCALPING WATCHLIST & REKAP HARIAN
# ============================================================================

def klasifikasi_risiko_bpjs(last: int, range_pct: float, val_billion: float) -> str:
    if last < 200 or range_pct >= 10.0 or val_billion < 20.0:
        return "highrisk"
    if last < 1000 or range_pct >= 6.0:
        return "medium risk"
    return "low risk"


def send_morning_watchlist(now: datetime, symbols: List[str], force: bool = False) -> None:
    if not force:
        return
    if not symbols:
        send_telegram("⚠️ Daftar watchlist kosong.")
        return

    log("Memindai kandidat Menu Pagi / BPJS...")
    kandidat = []
    for sym in symbols[:15]:
        if STOP_EVENT.is_set():
            break
        data = fetch_orderbook(sym)
        if not data or is_special_board(data):
            continue

        last = safe_int(safe_get_field(data, ("lastprice", "lastPrice", "last", "close")))
        high = safe_int(safe_get_field(data, ("high", "highPrice", "highest")))
        low = safe_int(safe_get_field(data, ("low", "lowPrice", "lowest")))
        prev = get_previous_close(data) or low
        if last <= 0 or high <= low or prev <= 0:
            continue

        val_idr = get_daily_value(data, last)
        val_billion = val_idr / 1_000_000_000
        range_pct = ((high - low) / low) * 100.0
        chg_pct = ((last - prev) / prev) * 100.0
        close_pos = (last - low) / (high - low)

        if val_billion >= 10.0 and range_pct >= 4.0 and 2.0 <= chg_pct <= 18.0 and close_pos >= 0.65:
            skor = (range_pct * 2.0) + min(val_billion / 10.0, 10.0) + chg_pct
            kandidat.append((skor, sym, last, high, low, chg_pct, range_pct, val_billion))
        STOP_EVENT.wait(0.15)

    if not kandidat:
        log("Tidak ada saham di screener yang memenuhi kriteria BPJS.")
        send_telegram("ℹ️ Belum ada saham di screener yang memenuhi kriteria BPJS.")
        return

    kandidat.sort(reverse=True)
    top3 = kandidat[:3]
    lines = []

    for _, sym, last, high, low, chg_pct, range_pct, val_b in top3:
        risiko = klasifikasi_risiko_bpjs(last, range_pct, val_b)
        label_header = f"${sym} (BPJS highrisk)" if risiko == "highrisk" else f"${sym} (BPJS)"

        entry_1 = add_ticks(high, 1)
        entry_2 = add_ticks(high, 2)
        tp1 = add_ticks(entry_2, 4)
        tp2 = add_ticks(entry_2, 8)

        raw_sl = int(round(entry_1 * 0.98))
        sl_by_tick = add_ticks(entry_1, -3)
        sl_price = min(raw_sl, sl_by_tick)
        step = tick_size(sl_price)
        sl_price = (sl_price // step) * step

        lines.append(
            f"{label_header}\n"
            f"Entry : {entry_1}-{entry_2}\n"
            f"TP area : {tp1} - {tp2}\n"
            f"SL : < {sl_price}"
        )

    lines.append("DYOR")
    send_telegram("\n\n".join(lines))
    log("Menu Pagi / BPJS berhasil dikirim via perintah /pagi.")



def sweep_expired_eod() -> None:
    for state in STORE.active_signals():
        last_ref = int(state.get("current_last") or state.get("last_at_alert") or 0)
        finalize_signal(state, "EXPIRED", last_ref)

def send_daily_report(now: datetime) -> None:
    report_date = now.date().isoformat()
    if STORE.report_sent(report_date):
        return
    stats = STORE.daily_stats(now.date())
    closed = stats["tp"] + stats["cl"]
    winrate = (stats["tp"] / closed * 100.0) if closed else 0.0
    tag = mode_prefix()

    nama_hari = ["Senin", "Selasa", "Rabu", "Kamis", "Jumat", "Sabtu", "Minggu"]
    nama_bulan = [
        "", "Januari", "Februari", "Maret", "April", "Mei", "Juni",
        "Juli", "Agustus", "September", "Oktober", "November", "Desember"
    ]
    tgl_label = f"{nama_hari[now.weekday()]}, {now.day} {nama_bulan[now.month]} {now.year}"

    start_ts = datetime.combine(now.date(), dtime.min, WIB).timestamp()
    end_ts = datetime.combine(now.date() + timedelta(days=1), dtime.min, WIB).timestamp()
    with STORE.lock:
        rows = STORE.conn.execute(
            "SELECT state_json FROM signals WHERE status IN ('TP','CL') AND closed_at>=? AND closed_at<? ORDER BY closed_at ASC",
            (start_ts, end_ts),
        ).fetchall()

    rincian = []
    for r in rows:
        try:
            s = json.loads(r["state_json"])
            ikon = "✅" if s.get("status") == "TP" else "❌"
            ref = s.get("entry") if s.get("kind") == "BO" else s.get("p1")
            last_c = s.get("last_at_close", "-")
            rincian.append(f"• ${s['symbol']} ({s['kind']}) — {ikon} {s['status']} ({ref} → {last_c})")
        except Exception:
            continue

    blok_rincian = "\n".join(rincian) if rincian else "• Belum ada sinyal yang menyentuh TP/CL hari ini."
    message = (
        f"📊 {tag}REKAP HARIAN\n"
        f"{tgl_label}\n\n"
        f"✅ TP: {stats['tp']} | ❌ CL: {stats['cl']}\n"
        f"⛔ Exp/Miss: {stats['expired']} | 🎯 WR: {winrate:.0f}%\n\n"
        f"Rincian Hasil:\n{blok_rincian}"
    )
    message_id = send_telegram(message, topic_id=TOPIC_WINRATE_ID or TOPIC_ID)
    if message_id:
        STORE.mark_report_sent(report_date)
        log("Rekap harian berhasil dikirim.")



def build_watchlist(current: List[str]) -> List[str]:
    active_symbols = {s["symbol"] for s in STORE.active_signals()}
    combined = []
    for symbol in current:
        if (
            symbol not in combined
            and symbol not in active_symbols
            and symbol not in BLACKLIST_402
            and symbol not in EXCLUDED_SYMBOLS
        ):
            combined.append(symbol)
    return combined


def handle_shutdown_signal(signum, _frame) -> None:
    log(f"Sinyal berhenti diterima ({signum}), menutup bot dengan bersih...")
    STOP_EVENT.set()
    # Beri waktu thread lain menyelesaikan iterasi terakhir, lalu paksa keluar
    threading.Timer(20.0, lambda: os._exit(0)).start()

from http.server import BaseHTTPRequestHandler, HTTPServer

class HealthCheckHandler(BaseHTTPRequestHandler):
    def do_GET(self):
        self.send_response(200)
        self.send_header("Content-type", "text/plain")
        self.end_headers()
        self.wfile.write(b"Sedayu Scalping Bot is Running!")

    def log_message(self, format, *args):
        pass  # Matikan log HTTP spam agar konsol bersih


def start_keepalive_server() -> None:
    port = int(os.environ.get("PORT", 10000))
    server = HTTPServer(("0.0.0.0", port), HealthCheckHandler)
    threading.Thread(target=server.serve_forever, daemon=True).start()
    log(f"Keep-alive web server berjalan di port {port}")

def main() -> None:
    global CURRENT_WATCHLIST_SHARED
    signal.signal(signal.SIGINT, handle_shutdown_signal)
    if hasattr(signal, "SIGTERM"):
        signal.signal(signal.SIGTERM, handle_shutdown_signal)

    log("=" * 60)
    mode_label = "LIVE MODE (PRODUKSI)" if LIVE_MODE else "TEST MODE (SIMULASI)"
    log(f"SEDAYU SCALPING BOT STARTED | {mode_label}")
    log(f"Worker: {JUMLAH_WORKER} | Slow-Lane: {SCAN_INTERVAL_SECONDS}s | Fast-Lane: {FAST_LANE_INTERVAL_SECONDS}s (Paralel)")

    if not BEARER_TOKEN:
        log("Bearer token belum siap. Isi token.txt lalu jalankan ulang.")
        return
    if not telegram_ready():
        log("PERINGATAN: telegram_token / chat_id di config.json belum diisi.")

    fast_thread = threading.Thread(target=fast_lane_loop, daemon=True)
    fast_thread.start()
    
    cmd_thread = threading.Thread(target=telegram_command_loop, daemon=True)
    cmd_thread.start()

    start_keepalive_server()


    screener_symbols = [] if MODE_CAKUPAN.strip().upper() == "CUSTOM" else fetch_screener_with_fallback()
    current_watchlist = resolve_universe(screener_symbols)
    with LOCK:
        CURRENT_WATCHLIST_SHARED = current_watchlist[:]

    log(f"Watchlist ({len(current_watchlist)}): {', '.join(current_watchlist)}")
    send_telegram(f" {mode_prefix()}BOT AKTIF ({len(current_watchlist)} saham)")

    last_screener_update = time.time()
    last_cleanup_date = now_wib().strftime("%Y-%m-%d")
    last_status = ""
    cycle = 0
    lunch_reset_date = ""

    executor = ThreadPoolExecutor(max_workers=JUMLAH_WORKER)
    try:
        while not STOP_EVENT.is_set():
            cycle_start = time.time()
            now = now_wib()
            today_str = now.strftime("%Y-%m-%d")

            if today_str != last_cleanup_date:
                cleanup_daily_memory(today_str, current_watchlist)
                last_cleanup_date = today_str
                log("Memori harian & BLACKLIST_402 dibersihkan.")

            check_premarket_token(now)
            if now.hour == 13 and 25 <= now.minute <= 29 and lunch_reset_date != today_str:
                with LOCK:
                    PRICE_HISTORY.clear()
                lunch_reset_date = today_str
                log("Memori pantulan harga pagi dibersihkan sebelum Sesi II.")

            if AUTH_EXPIRED.is_set():
                if last_status != "AUTH_EXPIRED":
                    log("Scanner berhenti sementara: Token Stockbit expired.")
                    last_status = "AUTH_EXPIRED"
                STOP_EVENT.wait(30)
                continue

            market_open, market_status = in_regular_market_hours(now)
            if not market_open:
                if LIVE_MODE and now.weekday() < 5 and now.date() not in HOLIDAYS:
                    if now.hour > 15 or (now.hour == 15 and now.minute >= 50):
                        sweep_expired_eod()
                    if now.hour > 16 or (now.hour == 16 and now.minute >= 5):
                        send_daily_report(now)
                if last_status != market_status:
                    log(market_status)
                    last_status = market_status
                STOP_EVENT.wait(15)
                continue

            if SCAN_PAUSED.is_set():
                if last_status != "PAUSED":
                    log("Radar dijeda sementara (/pause). Sinyal aktif tetap dipantau Fast-Lane.")
                    last_status = "PAUSED"
                STOP_EVENT.wait(5)
                continue

            if last_status != market_status:
                log(market_status)
                last_status = market_status

            if MODE_CAKUPAN.strip().upper() != "CUSTOM" and time.time() - last_screener_update >= UPDATE_SCREENER_SECONDS:
                new_symbols = fetch_screener_with_fallback()
                if new_symbols:
                    new_list = resolve_universe(new_symbols)
                    if new_list:
                        current_watchlist = new_list
                        with LOCK:
                            CURRENT_WATCHLIST_SHARED = current_watchlist[:]
                last_screener_update = time.time()

            symbols = build_watchlist(current_watchlist)
            cycle += 1
            futures = [executor.submit(process_symbol, symbol, False) for symbol in symbols]
            for future in as_completed(futures):
                if STOP_EVENT.is_set():
                    break
                try:
                    future.result()
                except Exception as exc:
                    log(f"Worker error: {type(exc).__name__}: {exc}")

            if STOP_EVENT.is_set():
                break

            elapsed = time.time() - cycle_start
            log(f"Siklus #{cycle} selesai: {len(symbols)} saham, {elapsed:.1f}s")

            sleep_for = max(1.0, SCAN_INTERVAL_SECONDS - elapsed)
            STOP_EVENT.wait(sleep_for)

    finally:
        executor.shutdown(wait=False, cancel_futures=True)
    fast_thread.join(timeout=3)
    cmd_thread.join(timeout=3)
    log("Bot berhenti sepenuhnya dengan bersih.")


if __name__ == "__main__":
    try:
        main()
    except KeyboardInterrupt:
        STOP_EVENT.set()
        log("Bot dihentikan oleh user (Ctrl+C).")
    except Exception as fatal:
        STOP_EVENT.set()
        log(f"FATAL: {type(fatal).__name__}: {fatal}")
        raise
