"""
PRIORITIES - a cooperative party game of extreme honesty and absurd choices.
Multiplayer for 2 or more players (no upper limit). Pure Python standard library.

Run:   python priorities.py [port]   (priorities.html must sit next to this file)
Then everyone on the same Wi-Fi opens the printed URL in a browser.
"""
import json
import os
import random
import secrets
import socket
import sys
import threading
import time
from collections import Counter
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from urllib.parse import urlparse, parse_qs

PORT = int(sys.argv[1]) if len(sys.argv) > 1 else 8000
HAND_SIZE = 5
WORD = "PRIORITIES"
NEEDED = Counter(WORD)
ACTIVE_TIMEOUT = 15  # seconds without a poll before a player counts as "away"

CARD_TEXT = """
Hawaiian pizza|Selfies|Long hugs|Kittens|Puppies|Netflix|Smelly socks|Spray cheese|Recycling|Spicy food
Karaoke|Camping|Rollercoasters|Sushi|Monday mornings|Naps|Breakfast in bed|Rain|Thunderstorms|Snow days
Beach holidays|Road trips|Air travel|Board games|Video games|Reality TV|Musicals|Horror movies|Rom-coms|Documentaries
Podcasts|Audiobooks|Libraries|Museums|Opera|Jazz|Heavy metal|Country music|Classical music|Disco
Line dancing|Yoga|Running|The gym|Swimming|Golf|Football|Cricket|Chess|Crosswords
Jigsaw puzzles|Knitting|Gardening|Cooking|Baking|Washing up|Ironing|Vacuuming|Laundry|Online shopping
Shopping malls|Black Friday|Coupons|Garage sales|Thrift shops|Tattoos|Piercings|Beards|Moustaches|Man buns
Socks with sandals|Onesies|Pyjamas|High heels|Flip-flops|Crocs|Bow ties|Fancy dress|Halloween|Christmas
Birthdays|New Year's Eve|Valentine's Day|Weddings|Baby showers|Surprise parties|Small talk|Gossip|Drama|Sarcasm
Puns|Dad jokes|Practical jokes|Tickling|Public speaking|Job interviews|The dentist|Spiders|Snakes|Clowns
Heights|Mice|Pigeons|Seagulls|Goldfish|Horses|Penguins|Sloths|Dolphins|Bees
Mosquitoes|Wasps|Coffee|Tea|Energy drinks|Craft beer|Red wine|Champagne|Cocktails|Smoothies
Kale|Brussels sprouts|Marmite|Olives|Mushrooms|Coriander|Garlic|Blue cheese|Anchovies|Liver
Tofu|Avocado toast|Fast food|Fish and chips|Hot dogs|Tacos|Curry|Ice cream|Chocolate|Doughnuts
Candy floss|Popcorn|Cereal for dinner|Leftovers|Brunch|Buffets|Vegetarianism|Diets|Social media|Smartphones
Emojis|Group chats|Voicemail|Phone calls|Video calls|Emails|Handwritten letters|Influencers|Celebrities|Royalty
Politicians|Millennials|Gen Z|Boomers|Teenagers|Toddlers|In-laws|Neighbours|Climate change|Electric cars
Cyclists|Traffic jams|Public transport|Queuing|Tipping|Self-checkouts|Robots|Artificial intelligence|Space travel|Aliens
Ghosts|Horoscopes|Conspiracy theories|Lottery tickets|Money|Fame|Alarm clocks|Early nights|Lie-ins|Sunrises
Bubble baths|Saunas|Massages|Fake tan|Glitter|Scented candles|Houseplants|Flat-pack furniture|Minimalism|Clutter
Cats|Dogs|Dating apps|Blind dates|Kissing|Cuddling|Skydiving|Theme parks|Fireworks|Barbecues
"""


def build_cards():
    texts = []
    for t in CARD_TEXT.replace("\n", "|").split("|"):
        t = t.strip()
        if t and t not in texts:
            texts.append(t)
    # Letters cycle through PRIORITIES so the deck's letter mix matches the word
    return [{"id": i + 1, "text": t, "letter": WORD[i % len(WORD)]} for i, t in enumerate(texts)]


CARDS = build_cards()
CARD_BY_ID = {c["id"]: c for c in CARDS}


def can_spell(letters):
    have = Counter(letters)
    return all(have[ch] >= n for ch, n in NEEDED.items())


def progress(letters):
    have = Counter(letters)
    out = []
    for ch in WORD:
        if have[ch] > 0:
            have[ch] -= 1
            out.append(True)
        else:
            out.append(False)
    return out


class Game:
    def __init__(self):
        self.players = []  # {id, name, token, last_seen}
        self.host = None
        self.next_pid = 1
        self.draw_pile = []  # shared across games; refilled only after every card has been dealt
        self.to_lobby()

    # ---------- helpers ----------
    def to_lobby(self):
        self.phase = "lobby"
        self.hand = []
        self.secret = None
        self.group = []
        self.agreed = set()
        self.turn = 0
        self.target_id = None
        self.round = 0
        self.players_pile = []
        self.game_pile = []
        self.result = None
        self.winner = None
        self.distance_total = 0
        self.history = []
        self.log = []

    def add_log(self, msg):
        self.log.append(msg)
        self.log = self.log[-10:]

    def by_token(self, token):
        return next((p for p in self.players if token and p["token"] == token), None)

    def by_id(self, pid):
        return next((p for p in self.players if p["id"] == pid), None)

    def name_of(self, pid):
        p = self.by_id(pid)
        return p["name"] if p else "?"

    def active(self, p):
        return time.time() - p["last_seen"] < ACTIVE_TIMEOUT

    def draw(self, n):
        if len(self.draw_pile) < n:
            leftover = self.draw_pile
            fresh = [c["id"] for c in CARDS if c["id"] not in leftover]
            random.shuffle(fresh)
            self.draw_pile = leftover + fresh  # finish the old cycle before the new one starts
            self.add_log("Every card has been played - reshuffling the full deck.")
        hand, self.draw_pile = self.draw_pile[:n], self.draw_pile[n:]
        return hand

    def guessers(self):
        return [p for p in self.players if p["id"] != self.target_id]

    # ---------- lifecycle ----------
    def join(self, name):
        name = " ".join(name.split())[:20]
        if not name:
            return {"error": "Enter a name."}
        existing = next((p for p in self.players if p["name"].lower() == name.lower()), None)
        if existing:
            if self.active(existing):
                return {"error": "That name is taken."}
            existing["token"] = secrets.token_hex(12)  # reclaim a seat after a lost tab
            existing["last_seen"] = time.time()
            self.add_log(f"{name} rejoined.")
            return {"token": existing["token"]}
        p = {"id": self.next_pid, "name": name, "token": secrets.token_hex(12), "last_seen": time.time()}
        self.next_pid += 1
        self.players.append(p)
        if self.host is None:
            self.host = p["id"]
        self.add_log(f"{name} joined.")
        return {"token": p["token"]}

    def remove(self, pid):
        p = self.by_id(pid)
        if not p:
            return
        idx = self.players.index(p)
        self.players.remove(p)
        self.agreed.discard(pid)
        if idx < self.turn:
            self.turn -= 1
        if self.host == pid:
            self.host = self.players[0]["id"] if self.players else None
        self.add_log(f"{p['name']} left.")
        if self.phase in ("ranking", "guessing", "reveal") and len(self.players) < 2:
            self.add_log("Not enough players - back to the lobby.")
            self.to_lobby()
        elif self.phase in ("ranking", "guessing") and pid == self.target_id:
            self.add_log("The Target Player left - dealing a new round.")
            self.new_round()
        else:
            self.check_consensus()

    def start(self):
        self.to_lobby()
        self.turn = random.randrange(len(self.players))
        self.add_log("Game started! Spell PRIORITIES before the game does.")
        self.new_round()

    def new_round(self):
        if len(self.players) < 2:
            self.to_lobby()
            return
        self.turn %= len(self.players)
        self.target_id = self.players[self.turn]["id"]
        self.hand = self.draw(HAND_SIZE)
        self.secret = None
        self.group = list(self.hand)
        self.agreed = set()
        self.result = None
        self.round += 1
        self.phase = "ranking"
        self.add_log(f"Round {self.round}: {self.name_of(self.target_id)} is the Target Player.")

    def check_consensus(self):
        if self.phase != "guessing":
            return
        live = [p for p in self.guessers() if self.active(p)]
        if live and all(p["id"] in self.agreed for p in live):
            self.reveal()

    def reveal(self):
        cards, dist, correct = [], 0, 0
        for gi, cid in enumerate(self.group):
            ti = self.secret.index(cid)
            ok = gi == ti
            correct += ok
            dist += abs(gi - ti)
            c = CARD_BY_ID[cid]
            (self.players_pile if ok else self.game_pile).append(c["letter"])
            cards.append({"id": cid, "text": c["text"], "letter": c["letter"],
                          "guess_pos": gi + 1, "true_pos": ti + 1, "correct": ok})
        self.distance_total += dist
        self.result = {"cards": cards, "correct": correct, "distance": dist,
                       "target": self.name_of(self.target_id)}
        self.history.append({"round": self.round, "target": self.name_of(self.target_id),
                             "correct": correct, "distance": dist})
        self.add_log(f"Reveal! {correct}/5 correct for {self.name_of(self.target_id)}.")
        p_done, g_done = can_spell(self.players_pile), can_spell(self.game_pile)
        if p_done or g_done:
            self.winner = "players" if p_done else "game"  # same-round tie goes to the players
            self.phase = "over"
        else:
            self.phase = "reveal"

    # ---------- actions ----------
    def action(self, token, act, data):
        me = self.by_token(token)
        if not me:
            return "You are not in the game - please rejoin."
        me["last_seen"] = time.time()
        is_host = me["id"] == self.host
        is_target = me["id"] == self.target_id

        if act == "leave":
            self.remove(me["id"])
        elif act == "kick":
            if not is_host:
                return "Only the host can remove players."
            self.remove(int(data.get("pid", 0)))
        elif act == "start":
            if not is_host:
                return "Only the host can start."
            if len(self.players) < 2:
                return "Need at least 2 players."
            self.start()
        elif act == "lobby":
            if not is_host:
                return "Only the host can do that."
            self.to_lobby()
            self.add_log("Host returned everyone to the lobby.")
        elif act == "skip":
            if not is_host or self.phase not in ("ranking", "guessing"):
                return "Can't skip right now."
            self.turn += 1
            self.add_log("Host skipped the round.")
            self.new_round()
        elif act == "rank":
            if self.phase != "ranking" or not is_target:
                return "It's not your turn to rank."
            order = [int(x) for x in data.get("order", [])]
            if sorted(order) != sorted(self.hand):
                return "Invalid ranking."
            self.secret = order
            self.phase = "guessing"
            self.add_log(f"{me['name']} locked in a secret ranking. Group: discuss and agree!")
        elif act == "move":
            if self.phase != "guessing" or is_target:
                return "You can't move cards right now."
            cid, to = int(data.get("card", 0)), int(data.get("to", -1))
            if cid not in self.group or not 0 <= to < len(self.group):
                return "Invalid move."
            self.group.remove(cid)
            self.group.insert(to, cid)
            if self.agreed:
                self.agreed = set()
            self.add_log(f"{me['name']} moved “{CARD_BY_ID[cid]['text']}” to #{to + 1}.")
        elif act == "agree":
            if self.phase != "guessing" or is_target:
                return "You can't agree right now."
            if me["id"] in self.agreed:
                self.agreed.discard(me["id"])
            else:
                self.agreed.add(me["id"])
            self.check_consensus()
        elif act == "next":
            if self.phase != "reveal":
                return "Not ready for the next round."
            self.turn += 1
            self.new_round()
        else:
            return "Unknown action."
        return None

    # ---------- view ----------
    def view(self, token):
        me = self.by_token(token)
        if me:
            me["last_seen"] = time.time()
        self.check_consensus()
        is_target = bool(me and me["id"] == self.target_id)
        show_secret = self.phase in ("reveal", "over") or is_target
        live_guessers = [p for p in self.guessers() if self.active(p)] if self.target_id else []
        return {
            "phase": self.phase,
            "round": self.round,
            "me": {"id": me["id"], "name": me["name"], "is_host": me["id"] == self.host,
                   "is_target": is_target, "agreed": me["id"] in self.agreed} if me else None,
            "players": [{"id": p["id"], "name": p["name"], "active": self.active(p),
                         "host": p["id"] == self.host, "target": p["id"] == self.target_id,
                         "agreed": p["id"] in self.agreed} for p in self.players],
            "target_id": self.target_id,
            "target_name": self.name_of(self.target_id) if self.target_id else None,
            "hand": [{"id": c, "text": CARD_BY_ID[c]["text"]} for c in self.hand],
            "group": self.group,
            "secret": self.secret if show_secret else None,
            "agreed_count": len([p for p in live_guessers if p["id"] in self.agreed]),
            "guessers_live": len(live_guessers),
            "result": self.result,
            "players_pile": self.players_pile,
            "game_pile": self.game_pile,
            "players_progress": progress(self.players_pile),
            "game_progress": progress(self.game_pile),
            "winner": self.winner,
            "distance_total": self.distance_total,
            "history": self.history,
            "deck_left": len(self.draw_pile),
            "log": self.log,
        }


game = Game()
lock = threading.Lock()

HTML_FILE = os.path.join(os.path.dirname(os.path.abspath(__file__)), "priorities.html")


class Handler(BaseHTTPRequestHandler):
    def log_message(self, *args):
        pass

    def send(self, body, ctype="application/json", code=200):
        data = body if isinstance(body, bytes) else body.encode("utf-8")
        self.send_response(code)
        self.send_header("Content-Type", ctype + "; charset=utf-8")
        self.send_header("Cache-Control", "no-store")
        self.send_header("Content-Length", str(len(data)))
        self.end_headers()
        self.wfile.write(data)

    def do_GET(self):
        u = urlparse(self.path)
        if u.path in ("/", "/index.html"):
            with open(HTML_FILE, "rb") as f:  # re-read each time so edits show on refresh
                self.send(f.read(), "text/html")
        elif u.path == "/api/state":
            token = parse_qs(u.query).get("token", [""])[0]
            with lock:
                v = game.view(token)
            self.send(json.dumps(v))
        else:
            self.send(json.dumps({"error": "not found"}), code=404)

    def do_POST(self):
        u = urlparse(self.path)
        try:
            n = int(self.headers.get("Content-Length", 0))
            data = json.loads(self.rfile.read(n) or b"{}")
        except (ValueError, json.JSONDecodeError):
            self.send(json.dumps({"error": "bad request"}), code=400)
            return
        with lock:
            if u.path == "/api/join":
                res = game.join(str(data.get("name", "")))
            elif u.path == "/api/action":
                token = str(data.get("token", ""))
                try:
                    err = game.action(token, str(data.get("action", "")), data)
                except (ValueError, TypeError):
                    err = "Invalid request."
                res = {"error": err} if err else {"state": game.view(token)}
            else:
                res = {"error": "not found"}
        self.send(json.dumps(res))


def lan_ip():
    s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
    try:
        s.connect(("10.255.255.255", 1))  # no packets are sent; just picks the LAN interface
        return s.getsockname()[0]
    except OSError:
        return "127.0.0.1"
    finally:
        s.close()


if __name__ == "__main__":
    server = ThreadingHTTPServer(("0.0.0.0", PORT), Handler)
    print(f"PRIORITIES server running with {len(CARDS)} cards.")
    print(f"  On this computer:      http://localhost:{PORT}")
    print(f"  Other players (Wi-Fi): http://{lan_ip()}:{PORT}")
    print("Press Ctrl+C to stop.")
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        print("\nBye!")
