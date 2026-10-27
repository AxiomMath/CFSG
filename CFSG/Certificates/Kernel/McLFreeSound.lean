module

public import CFSG.Certificates.Kernel.McL.Sub
public import CFSG.Certificates.Kernel.LceSTabSound
public import CFSG.Certificates.Kernel.LceSP.Base
import CFSG.Certificates.Kernel.HOrbSound
import CFSG.Certificates.Kernel.LceSP.Walk
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.Certificates.McLFree

open CFSG.KC CFSG.Certificates.LCE

section

variable {G : Type*} [Group G] (gen : ℕ → G)

@[expose] noncomputable def pV (v : ℕ) : G := LceP.bv gen (McL.Sub.pw v) (McL.Sub.pn v)

theorem pk_spec {n W : ℕ} (hn : n < 65536) :
    McL.Sub.pn (McL.Sub.pk n W) = n ∧ McL.Sub.pw (McL.Sub.pk n W) = W := by
  have e : McL.Sub.pk n W = n + W * 2 ^ 16 := LceP.lor_shl (k := 16) (by norm_num; omega)
  constructor
  · change Nat.land (McL.Sub.pk n W) 65535 = n
    rw [LceP.land_lit _ 16 65535 (by norm_num), e]
    omega
  · change Nat.shiftRight (McL.Sub.pk n W) 16 = W
    rw [LceP.shr_eq, e]
    omega

theorem pn_lt (v : ℕ) : McL.Sub.pn v < 65536 := by
  change Nat.land v 65535 < 65536
  rw [LceP.land_lit _ 16 65535 (by norm_num)]
  omega

theorem wLen_lt (e : ℕ) : LceS.wLen e < 1024 := by
  change Nat.land (Nat.shiftRight e 2) 1023 < 1024
  rw [LceP.land_lit _ 10 1023 (by norm_num)]
  omega

theorem ofEnt_spec (e : ℕ) : McL.Sub.pn (McL.Sub.ofEnt e) = LceS.wLen e ∧
    McL.Sub.pw (McL.Sub.ofEnt e) = LceS.wWord e :=
  pk_spec (by have := wLen_lt e; omega)

theorem ofEnt_val (e : ℕ) :
    pV gen (McL.Sub.ofEnt e) = bval gen (LceS.wWord e) (LceS.wLen e) := by
  obtain ⟨h1, h2⟩ := ofEnt_spec e
  unfold pV
  rw [h1, h2]
  rfl

theorem cat_eq {a b : ℕ} (ha : McL.Sub.pw a < 256 ^ McL.Sub.pn a) :
    McL.Sub.cat a b = McL.Sub.pk (McL.Sub.pn a + McL.Sub.pn b)
      (McL.Sub.pw a + McL.Sub.pw b * 256 ^ McL.Sub.pn a) := by
  have hW : Nat.lor (McL.Sub.pw a) (Nat.shiftLeft (McL.Sub.pw b) (Nat.mul 8 (McL.Sub.pn a))) =
      McL.Sub.pw a + McL.Sub.pw b * 256 ^ McL.Sub.pn a := by
    rw [LceP.lor_shl (by change _ < 2 ^ (8 * _); rw [LceP.two_pow_eight_mul]; exact ha)]
    change _ + _ * 2 ^ (8 * _) = _
    rw [LceP.two_pow_eight_mul]
  unfold McL.Sub.cat
  rw [← hW]
  rfl

theorem cat_spec {a b : ℕ} (ha : McL.Sub.pw a < 256 ^ McL.Sub.pn a)
    (hb : McL.Sub.pw b < 256 ^ McL.Sub.pn b) (hn : McL.Sub.pn a + McL.Sub.pn b < 65536) :
    McL.Sub.pn (McL.Sub.cat a b) = McL.Sub.pn a + McL.Sub.pn b ∧
      McL.Sub.pw (McL.Sub.cat a b) < 256 ^ McL.Sub.pn (McL.Sub.cat a b) ∧
      pV gen (McL.Sub.cat a b) = pV gen a * pV gen b := by
  obtain ⟨h1, h2⟩ := pk_spec (W := McL.Sub.pw a + McL.Sub.pw b * 256 ^ McL.Sub.pn a) hn
  rw [cat_eq ha]
  unfold pV
  rw [h1, h2]
  refine ⟨rfl, ?_, LceP.bv_concat gen ha⟩
  calc McL.Sub.pw a + McL.Sub.pw b * 256 ^ McL.Sub.pn a
      < 256 ^ McL.Sub.pn a + McL.Sub.pw b * 256 ^ McL.Sub.pn a := by omega
    _ = (McL.Sub.pw b + 1) * 256 ^ McL.Sub.pn a := by ring
    _ ≤ 256 ^ McL.Sub.pn b * 256 ^ McL.Sub.pn a := Nat.mul_le_mul_right _ (by omega)
    _ = 256 ^ (McL.Sub.pn a + McL.Sub.pn b) := by ring

theorem cat_let {a b : ℕ} (ha : McL.Sub.pw a < 256 ^ McL.Sub.pn a)
    (hn : McL.Sub.pn a + McL.Sub.pn b < 65536) (q : ℕ) :
    wLet (McL.Sub.pw (McL.Sub.cat a b)) q = if q < McL.Sub.pn a then wLet (McL.Sub.pw a) q
      else wLet (McL.Sub.pw b) (q - McL.Sub.pn a) := by
  obtain ⟨-, h2⟩ := pk_spec (W := McL.Sub.pw a + McL.Sub.pw b * 256 ^ McL.Sub.pn a) hn
  rw [cat_eq ha, h2, LceP.wLet_eq, LceP.byte_concat ha, LceP.wLet_eq, LceP.wLet_eq]

@[expose] noncomputable def substAt (F : ℕ → ℕ) (v q : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) (McL.Sub.pk (nat_lit 0) (nat_lit 0))
    (fun q acc => McL.Sub.cat acc (F (wLet (McL.Sub.pw v) q))) q

theorem substAt_spec {F : ℕ → ℕ} {b : ℕ}
    (hF : ∀ c < 256, McL.Sub.pn (F c) < 16 ∧ McL.Sub.pw (F c) < 256 ^ McL.Sub.pn (F c))
    (hb : ∀ c < 256, ∀ i < McL.Sub.pn (F c), wLet (McL.Sub.pw (F c)) i < b) (v : ℕ) :
    ∀ q, q < 4096 →
      McL.Sub.pn (substAt F v q) ≤ 15 * q ∧
      McL.Sub.pw (substAt F v q) < 256 ^ McL.Sub.pn (substAt F v q) ∧
      (∀ i < McL.Sub.pn (substAt F v q), wLet (McL.Sub.pw (substAt F v q)) i < b) ∧
      pV gen (substAt F v q) =
        ((List.range q).map fun i => pV gen (F (wLet (McL.Sub.pw v) i))).prod
  | 0, _ => by
    obtain ⟨h1, h2⟩ := pk_spec (n := 0) (W := 0) (by norm_num)
    have e : substAt F v 0 = McL.Sub.pk 0 0 := rfl
    rw [e]
    unfold pV
    rw [h1, h2]
    exact ⟨by omega, by norm_num, fun i hi => absurd hi (Nat.not_lt_zero _), rfl⟩
  | q + 1, hq => by
    obtain ⟨h1, h2, h3, h4⟩ := substAt_spec hF hb v q (by omega)
    have e : substAt F v (q + 1) = McL.Sub.cat (substAt F v q) (F (wLet (McL.Sub.pw v) q)) := rfl
    obtain ⟨f1, f2⟩ := hF _ (LceP.wLet_lt (McL.Sub.pw v) q)
    have hn : McL.Sub.pn (substAt F v q) + McL.Sub.pn (F (wLet (McL.Sub.pw v) q)) < 65536 := by
      omega
    obtain ⟨c1, c2, c3⟩ := cat_spec gen h2 f2 hn
    rw [e]
    refine ⟨by rw [c1]; omega, c2, ?_, ?_⟩
    · intro i hi
      rw [cat_let h2 hn]
      split_ifs with hi'
      · exact h3 i hi'
      · exact hb _ (LceP.wLet_lt (McL.Sub.pw v) q) _ (by rw [c1] at hi; omega)
    · rw [c3, h4, List.range_succ, List.map_append, List.prod_append]
      simp

theorem subst_spec {F : ℕ → ℕ} {b v : ℕ}
    (hF : ∀ c < 256, McL.Sub.pn (F c) < 16 ∧ McL.Sub.pw (F c) < 256 ^ McL.Sub.pn (F c))
    (hb : ∀ c < 256, ∀ i < McL.Sub.pn (F c), wLet (McL.Sub.pw (F c)) i < b)
    (hv : McL.Sub.pn v < 4096) :
    McL.Sub.pn (McL.Sub.subst F v) ≤ 15 * McL.Sub.pn v ∧
      McL.Sub.pw (McL.Sub.subst F v) < 256 ^ McL.Sub.pn (McL.Sub.subst F v) ∧
      (∀ i < McL.Sub.pn (McL.Sub.subst F v), wLet (McL.Sub.pw (McL.Sub.subst F v)) i < b) ∧
      pV gen (McL.Sub.subst F v) =
        ((List.range (McL.Sub.pn v)).map fun i => pV gen (F (wLet (McL.Sub.pw v) i))).prod :=
  substAt_spec gen hF hb v _ hv

@[expose] noncomputable def pinvAt (v q : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) (nat_lit 0)
    (fun q acc => Nat.lor acc (Nat.shiftLeft (Nat.xor (wLet (McL.Sub.pw v) q) (nat_lit 1))
      (Nat.mul (nat_lit 8) (Nat.sub (Nat.sub (McL.Sub.pn v) q) (nat_lit 1))))) q

theorem pinvAt_spec (v : ℕ) : ∀ q ≤ McL.Sub.pn v, ∃ X, pinvAt v q = X * 256 ^ (McL.Sub.pn v - q) ∧
    X < 256 ^ q ∧ ∀ k < q, wLet X k = wLet (McL.Sub.pw v) (q - 1 - k) ^^^ 1
  | 0, _ => ⟨0, by rw [Nat.zero_mul]; rfl, by norm_num, fun k hk => absurd hk (Nat.not_lt_zero _)⟩
  | q + 1, hq => by
    obtain ⟨X, h1, h2, h3⟩ := pinvAt_spec v q (by omega)
    set n := McL.Sub.pn v
    set b := wLet (McL.Sub.pw v) q ^^^ 1
    have hb : b < 256 := Nat.xor_lt_two_pow (n := 8)
      (by have := LceP.wLet_lt (McL.Sub.pw v) q; norm_num; omega) (by norm_num)
    obtain ⟨s, hs⟩ : ∃ s, n - q = s + 1 := ⟨n - q - 1, by omega⟩
    have hs1 : Nat.sub (Nat.sub n q) 1 = s := by
      change n - q - 1 = s
      omega
    have hs2 : n - (q + 1) = s := by omega
    have e : pinvAt v (q + 1) = Nat.lor (pinvAt v q)
        (Nat.shiftLeft b (Nat.mul 8 (Nat.sub (Nat.sub n q) 1))) := rfl
    have e1 : X * 256 ^ (s + 1) = Nat.shiftLeft (Nat.shiftLeft X 8) (8 * s) := by
      change _ = (X <<< 8) <<< (8 * s)
      rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq, LceP.two_pow_eight_mul, pow_succ]
      ring
    have e2 : Nat.lor b (Nat.shiftLeft X 8) = b + X * 256 := by
      rw [LceP.lor_shl (by norm_num; omega)]
      norm_num
    refine ⟨b + X * 256, ?_, ?_, fun k hk => ?_⟩
    · rw [e, h1, hs1, hs, e1, hs2]
      change Nat.shiftLeft X 8 <<< (8 * s) ||| b <<< (8 * s) = _
      rw [← Nat.shiftLeft_or_distrib, Nat.or_comm]
      change Nat.shiftLeft (Nat.lor b (Nat.shiftLeft X 8)) (8 * s) = _
      rw [e2]
      change (b + X * 256) <<< (8 * s) = _
      rw [Nat.shiftLeft_eq, LceP.two_pow_eight_mul]
    · calc b + X * 256 < 256 + X * 256 := by omega
        _ = (X + 1) * 256 := by ring
        _ ≤ 256 ^ q * 256 := Nat.mul_le_mul_right _ (by omega)
        _ = 256 ^ (q + 1) := by ring
    · rw [LceP.wLet_eq]
      rcases k with _ | j
      · have e3 : q + 1 - 1 - 0 = q := by omega
        rw [pow_zero, Nat.div_one, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hb, e3]
      · have e3 : (b + X * 256) / 256 ^ (j + 1) = X / 256 ^ j := by
          rw [pow_succ', ← Nat.div_div_eq_div_mul]
          congr 1
          omega
        have e4 : q + 1 - 1 - (j + 1) = q - 1 - j := by omega
        rw [e3, ← LceP.wLet_eq, h3 j (by omega), e4]

theorem pinvW_spec (v : ℕ) : McL.Sub.pn (McL.Sub.pinvW v) = McL.Sub.pn v ∧
    McL.Sub.pw (McL.Sub.pinvW v) < 256 ^ McL.Sub.pn v ∧
    ∀ k < McL.Sub.pn v, wLet (McL.Sub.pw (McL.Sub.pinvW v)) k =
      wLet (McL.Sub.pw v) (McL.Sub.pn v - 1 - k) ^^^ 1 := by
  obtain ⟨X, h1, h2, h3⟩ := pinvAt_spec v (McL.Sub.pn v) le_rfl
  have e : McL.Sub.pinvW v = McL.Sub.pk (McL.Sub.pn v) (pinvAt v (McL.Sub.pn v)) := rfl
  rw [Nat.sub_self, pow_zero, Nat.mul_one] at h1
  obtain ⟨p1, p2⟩ := pk_spec (W := pinvAt v (McL.Sub.pn v)) (pn_lt v)
  rw [e, p1, p2, h1]
  exact ⟨rfl, h2, h3⟩

theorem pinvW_val {v : ℕ} (hv : ∀ q < McL.Sub.pn v, wLet (McL.Sub.pw v) q < 254) :
    pV gen (McL.Sub.pinvW v) = (pV gen v)⁻¹ := by
  obtain ⟨s1, -, s3⟩ := pinvW_spec v
  unfold pV
  rw [s1, LceP.bv, LceP.bv, List.prod_inv_reverse, List.map_map]
  change _ = ((List.range (McL.Sub.pn v)).map
    fun i => (LceP.lv gen (wLet (McL.Sub.pw v) i))⁻¹).reverse.prod
  rw [← HO.map_range_rev (fun i => (LceP.lv gen (wLet (McL.Sub.pw v) i))⁻¹) (McL.Sub.pn v)]
  congr 1
  apply List.map_congr_left
  intro k hk
  have hk' := List.mem_range.mp hk
  rw [s3 k hk', LceP.lv_xor_one gen (hv _ (by omega))]

theorem mkK_spec {c s : ℕ} (hc : c < 65536) :
    Bind.kCnt (Bind.mkK c s) = c ∧ Bind.kStk (Bind.mkK c s) = s := by
  have e : Bind.mkK c s = c + s * 2 ^ 16 := LceP.lor_shl (k := 16) (by norm_num; omega)
  constructor
  · change Nat.land (Bind.mkK c s) 65535 = c
    rw [LceP.land_lit _ 16 65535 (by norm_num), e]
    omega
  · change Nat.shiftRight (Bind.mkK c s) 16 = s
    rw [LceP.shr_eq, e]
    omega

@[expose] noncomputable def redAt (v q : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) (nat_lit 0)
    (fun q P => Bool.rec (motive := fun _ => ℕ) (Bind.push (nat_lit 1) P (wLet (McL.Sub.pw v) q)) P
      (Nat.beq (wLet (McL.Sub.pw v) q) (nat_lit 255))) q

theorem redAt_spec (v : ℕ) : ∀ q ≤ McL.Sub.pn v, ∃ l : List ℕ,
    redAt v q = Bind.mkK l.length (LceP.enc l) ∧ l.length ≤ q ∧ (∀ x ∈ l, x < 255) ∧
      LceP.lval gen l = LceP.bv gen (McL.Sub.pw v) q
  | 0, _ => ⟨[], rfl, le_rfl, by simp, rfl⟩
  | q + 1, hq => by
    obtain ⟨l, hl, hlen, hlt, hlv⟩ := redAt_spec v q (by omega)
    have hq' := pn_lt v
    have e : redAt v (q + 1) = Bool.rec (motive := fun _ => ℕ)
        (Bind.push 1 (redAt v q) (wLet (McL.Sub.pw v) q)) (redAt v q)
        (Nat.beq (wLet (McL.Sub.pw v) q) 255) := rfl
    rw [e, LceP.brec_eq, LceP.bv_succ, ← hlv, hl]
    set x := wLet (McL.Sub.pw v) q
    have hx := LceP.wLet_lt (McL.Sub.pw v) q
    split_ifs with h255
    · rw [Nat.beq_eq] at h255
      rw [h255, LceP.lv_255, mul_one]
      exact ⟨l, rfl, by omega, hlt, rfl⟩
    · rw [Nat.beq_eq] at h255
      obtain ⟨k1, k2⟩ := mkK_spec (s := LceP.enc l) (show l.length < 65536 by omega)
      unfold Bind.push
      rw [k1, k2, LceP.brec_eq]
      split_ifs with hc
      · simp only [LceP.andB_iff, Nat.blt_eq, Nat.beq_eq] at hc
        obtain ⟨hpos, htop⟩ := hc
        rcases l with _ | ⟨y, l'⟩
        · exact absurd hpos (by simp)
        · have hy := hlt y (by simp)
          have e1 : Nat.land (LceP.enc (y :: l')) 255 = y + 1 := by
            change (LceP.enc l' * 256 + (y + 1)) &&& (2 ^ 8 - 1) = _
            rw [Nat.and_two_pow_sub_one_eq_mod]
            omega
          rw [e1] at htop
          have hyx : y = x ^^^ 1 := by
            change y + 1 = Nat.xor x 1 + 1 at htop
            exact Nat.succ.inj htop
          have hx254 : x < 254 := by
            rcases Nat.lt_or_ge x 254 with h | h
            · exact h
            · exfalso
              have : x = 254 := by omega
              rw [this] at hyx
              have : (254 : ℕ) ^^^ 1 = 255 := by decide
              omega
          refine ⟨l', ?_, by simp at hlen ⊢; omega, fun z hz => hlt z (by simp [hz]), ?_⟩
          · have e2 : Nat.shiftRight (LceP.enc (y :: l')) 8 = LceP.enc l' := by
              change (LceP.enc l' * 256 + (y + 1)) >>> 8 = LceP.enc l'
              rw [Nat.shiftRight_eq_div_pow]
              omega
            have e3 : Nat.sub (y :: l').length 1 = l'.length := by simp
            rw [e2, e3]
          · rw [LceP.lval_cons, hyx, LceP.lv_xor_one gen hx254, mul_assoc, inv_mul_cancel, mul_one]
      · refine ⟨x :: l, ?_, by simp; omega, ?_, LceP.lval_cons gen _ _⟩
        · rfl
        · intro z hz
          rcases List.mem_cons.1 hz with rfl | hz
          · omega
          · exact hlt z hz

theorem red_spec (v : ℕ) : ∃ l : List ℕ, McL.Sub.red v = Bind.mkK l.length (LceP.enc l) ∧
    l.length ≤ McL.Sub.pn v ∧ (∀ x ∈ l, x < 255) ∧ LceP.lval gen l = pV gen v :=
  redAt_spec gen v (McL.Sub.pn v) le_rfl

theorem enc_inj : ∀ (l1 l2 : List ℕ), (∀ x ∈ l1, x < 255) → (∀ x ∈ l2, x < 255) →
    LceP.enc l1 = LceP.enc l2 → l1 = l2
  | [], [], _, _, _ => rfl
  | [], y :: l, _, _, h => by
    change 0 = LceP.enc l * 256 + (y + 1) at h
    omega
  | x :: l, [], _, _, h => by
    change LceP.enc l * 256 + (x + 1) = 0 at h
    omega
  | x :: l1, y :: l2, h1, h2, h => by
    have hx := h1 x (by simp)
    have hy := h2 y (by simp)
    change LceP.enc l1 * 256 + (x + 1) = LceP.enc l2 * 256 + (y + 1) at h
    have e1 : x = y := by omega
    have e2 : LceP.enc l1 = LceP.enc l2 := by omega
    rw [e1, enc_inj l1 l2 (fun z hz => h1 z (by simp [hz])) (fun z hz => h2 z (by simp [hz])) e2]

theorem redEq_val {u v : ℕ} (h : McL.Sub.redEq u v = true) : pV gen u = pV gen v := by
  obtain ⟨l1, h1, n1, b1, v1⟩ := red_spec gen u
  obtain ⟨l2, h2, n2, b2, v2⟩ := red_spec gen v
  have e : McL.Sub.red u = McL.Sub.red v := Nat.eq_of_beq_eq_true h
  rw [h1, h2] at e
  have hu := pn_lt u
  have hv := pn_lt v
  obtain ⟨-, s1⟩ := mkK_spec (c := l1.length) (s := LceP.enc l1) (by omega)
  obtain ⟨-, s2⟩ := mkK_spec (c := l2.length) (s := LceP.enc l2) (by omega)
  have he : LceP.enc l1 = LceP.enc l2 := by rw [← s1, ← s2, e]
  rw [← v1, ← v2, enc_inj l1 l2 b1 b2 he]

theorem enc_byte : ∀ (l : List ℕ), (∀ x ∈ l, x < 255) → ∀ i < l.length,
    LceP.enc l / 256 ^ i % 256 = l[i]! + 1
  | [], _, i, hi => absurd hi (Nat.not_lt_zero i)
  | y :: l, hl, i, hi => by
    have hy := hl y (by simp)
    rcases i with _ | i
    · change (LceP.enc l * 256 + (y + 1)) / 1 % 256 = y + 1
      omega
    · have := enc_byte l (fun z hz => hl z (by simp [hz])) i (by simpa using hi)
      change (LceP.enc l * 256 + (y + 1)) / 256 ^ (i + 1) % 256 = l[i]! + 1
      rw [pow_succ', ← Nat.div_div_eq_div_mul, show (LceP.enc l * 256 + (y + 1)) / 256 = LceP.enc l by
        omega]
      exact this

theorem stkW_spec {l : List ℕ} (hl : ∀ x ∈ l, x < 255) (hn : l.length < 65536) :
    McL.Sub.pn (McL.Sub.stkW (Bind.mkK l.length (LceP.enc l))) = l.length ∧
      (∀ q < l.length, wLet (McL.Sub.pw (McL.Sub.stkW (Bind.mkK l.length (LceP.enc l)))) q < 255) ∧
      pV gen (McL.Sub.stkW (Bind.mkK l.length (LceP.enc l))) = LceP.lval gen l := by
  obtain ⟨k1, k2⟩ := mkK_spec (s := LceP.enc l) hn
  set P := Bind.mkK l.length (LceP.enc l)
  set f : ℕ → ℕ := fun q => Bind.kByte P (l.length - (q + 1)) - 1
  have hbyte : ∀ i < l.length, Bind.kByte P i = l[i]! + 1 := by
    intro i hi
    change Nat.land (Nat.shiftRight (Bind.kStk P) (Nat.mul 8 i)) 255 = _
    rw [k2, LceP.land8, LceP.shr_eq]
    change LceP.enc l / 2 ^ (8 * i) % 256 = _
    rw [LceP.two_pow_eight_mul]
    exact enc_byte l hl i hi
  have hf : ∀ j, f j < 256 := fun j => by
    have := LceP.wLet_lt (Bind.kStk P) (l.length - (j + 1))
    change wLet (Bind.kStk P) (l.length - (j + 1)) - 1 < 256
    omega
  have e : McL.Sub.stkW P = McL.Sub.pk l.length (HO.byteFold f l.length) := by
    unfold McL.Sub.stkW
    rw [k1]
    rfl
  obtain ⟨hb1, hb2⟩ := HO.byteFold_spec f hf l.length
  obtain ⟨p1, p2⟩ := pk_spec (W := HO.byteFold f l.length) hn
  rw [e, p1, p2]
  refine ⟨rfl, fun q hq => ?_, ?_⟩
  · rw [LceP.wLet_eq, hb2 q hq]
    change Bind.kByte P (l.length - (q + 1)) - 1 < 255
    rw [hbyte _ (by omega)]
    have := hl (l[l.length - (q + 1)]!) (by
      rw [getElem!_pos l _ (by omega)]
      exact List.getElem_mem _)
    omega
  · unfold pV
    rw [p1, p2]
    rw [show LceP.bv gen (HO.byteFold f l.length) l.length =
      bval gen (HO.byteFold f l.length) l.length from rfl, HO.bval_byteFold gen f hf]
    unfold LceP.lval
    congr 1
    apply List.ext_getElem (by simp)
    intro q h1 h2
    have hq : q < l.length := by simpa using h1
    simp only [List.getElem_map, List.getElem_range, List.getElem_reverse]
    change LceP.lv gen (Bind.kByte P (l.length - (q + 1)) - 1) = LceP.lv gen _
    rw [hbyte _ (by omega), Nat.add_sub_cancel, getElem!_pos l _ (by omega)]
    congr 2
    omega

theorem conjRot_one {e ul U : ℕ}
    (hr : LceS.wWord e < 2 ^ (8 * LceS.wLen e) ∧ bval gen (LceS.wWord e) (LceS.wLen e) = 1)
    (hU : ∀ q < McL.Sub.pn U, wLet (McL.Sub.pw U) q < 255)
    (h : McL.Sub.isConjRot e ul U = true) : pV gen U = 1 := by
  unfold McL.Sub.isConjRot at h
  simp only [LceP.andB_iff, Nat.beq_eq, Nat.blt_eq] at h
  obtain ⟨hlen, hmir, -, hrot⟩ := h
  set m := LceS.wLen e
  set X := McL.Sub.pw U
  have hlen' : McL.Sub.pn U = ul + (m + ul) := by
    change McL.Sub.pn U = 2 * ul + m at hlen
    omega
  set A := X % 256 ^ ul
  set B := X / 256 ^ ul
  set M := B % 256 ^ m
  set C := B / 256 ^ m
  have hA : A < 256 ^ ul := Nat.mod_lt _ (by positivity)
  have hM : M < 256 ^ m := Nat.mod_lt _ (by positivity)
  have eX : X = A + B * 256 ^ ul := by rw [Nat.mul_comm]; exact (Nat.mod_add_div X _).symm
  have eB : B = M + C * 256 ^ m := by rw [Nat.mul_comm]; exact (Nat.mod_add_div B _).symm
  unfold pV
  change LceP.bv gen X (McL.Sub.pn U) = 1
  rw [hlen', eX, LceP.bv_concat gen hA, eB, LceP.bv_concat gen hM]
  have hmid : M = Nat.land (Nat.shiftRight X (Nat.mul 8 ul))
      (Nat.sub (Nat.shiftLeft 1 (Nat.mul 8 m)) 1) := by
    rw [LceP.land_mask, LceP.shr_eq]
    change B % 256 ^ m = X / 2 ^ (8 * ul) % 2 ^ (8 * m)
    rw [LceP.two_pow_eight_mul, LceP.two_pow_eight_mul]
  rw [← hmid] at hrot
  obtain ⟨s, hs, hseq⟩ := LceP.anyRec_iff _ m hrot
  rw [Nat.beq_eq] at hseq
  have hr' : LceS.wWord e < 256 ^ m := by rw [← LceP.two_pow_eight_mul]; exact hr.1
  have h1 : LceP.bv gen M m = 1 := by
    rw [← hseq]
    exact LceP.bv_rot gen hr' hs hr.2
  have hmir' := (LceP.allRec_iff (fun q => Nat.beq (Nat.xor (McL.Sub.pl U q) 1)
    (McL.Sub.pl U (Nat.sub (McL.Sub.pn U) (Nat.succ q)))) ul).1 hmir
  have hletA : ∀ q < ul, wLet A q = wLet X q := by
    intro q hq
    rw [LceP.wLet_eq, LceP.wLet_eq, eX]
    exact (HO.byte_add_high hq).symm
  have hletC : ∀ t < ul, wLet C t = wLet X (ul + m + t) := by
    intro t ht
    rw [LceP.wLet_eq, LceP.wLet_eq]
    rw [pow_add, pow_add, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul]
  have hA254 : ∀ q < ul, wLet A q < 254 := by
    intro q hq
    have hm := Nat.eq_of_beq_eq_true (hmir' q hq)
    rw [hletA q hq]
    have h2 := hU (ul + (m + ul) - (q + 1)) (by omega)
    change wLet X q ^^^ 1 = wLet X (McL.Sub.pn U - (q + 1)) at hm
    rw [hlen'] at hm
    rw [← hm] at h2
    have h3 := hU q (by omega)
    rcases Nat.lt_or_ge (wLet X q) 254 with h4 | h4
    · exact h4
    · have : wLet X q = 254 := by omega
      rw [this] at h2
      exact absurd h2 (by decide)
  have hC : LceP.bv gen C ul = (LceP.bv gen A ul)⁻¹ := by
    change bval gen C ul = (bval gen A ul)⁻¹
    rw [← HO.bval_invW gen (fun q hq => hA254 q hq)]
    apply HO.bval_congr gen
    intro k hk
    rw [HO.invW_eq, (HO.byteFold_spec _ (fun k => HO.byte_xor_lt A _) ul).2 k hk, ← LceP.wLet_eq,
      hletC k hk]
    change _ = wLet A (ul - 1 - k) ^^^ 1
    rw [hletA _ (by omega)]
    have hm := Nat.eq_of_beq_eq_true (hmir' (ul - 1 - k) (by omega))
    change wLet X (ul - 1 - k) ^^^ 1 = wLet X (McL.Sub.pn U - (ul - 1 - k + 1)) at hm
    rw [hm, hlen']
    congr 1
    omega
  rw [h1, hC, one_mul, mul_inv_cancel]

theorem conjRelOK_one {RT : ℕ → ℕ} {R r ul V : ℕ}
    (hRT : ∀ r < R, LceS.wWord (RT r) < 2 ^ (8 * LceS.wLen (RT r)) ∧
      bval gen (LceS.wWord (RT r)) (LceS.wLen (RT r)) = 1)
    (h : McL.Sub.conjRelOK RT R r ul V = true) : pV gen V = 1 := by
  obtain ⟨l, hl, hll, hlt, hlv⟩ := red_spec gen V
  obtain ⟨s1, s2, s3⟩ := stkW_spec gen hlt (by have := pn_lt V; omega)
  unfold McL.Sub.conjRelOK at h
  simp only [LceP.andB_iff, Nat.blt_eq] at h
  obtain ⟨hrR, hconj⟩ := h
  rw [hl] at hconj
  have h1 := conjRot_one gen (hRT r hrR) (fun q hq => s2 q (by rw [s1] at hq; exact hq)) hconj
  rw [s3, hlv] at h1
  exact h1

end

end CFSG.Certificates.McLFree

end
