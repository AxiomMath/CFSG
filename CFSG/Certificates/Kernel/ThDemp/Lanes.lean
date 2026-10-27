module

public import Certificates.Data.Kernel.ThDemp.Orb
public import CFSG.Certificates.Kernel.ThDemp.Rows
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.Certificates.ThDemp.Lanes

open CFSG.KC.Th CFSG.KC.Th.BigS CFSG.KC.ThDemp CFSG.KC.Loop CFSG.Certificates.ThDemp.Rows

set_option exponentiation.threshold 2000

@[expose] def lane (N j : ℕ) : ℕ := (N >>> (1280 * j)) % 2 ^ 1280

@[expose] def lane64 (N j : ℕ) : ℕ := (N >>> (64 * j)) % 2 ^ 64

theorem testBit_lane (N j i : ℕ) :
    (lane N j).testBit i = (decide (i < 1280) && N.testBit (1280 * j + i)) := by
  rw [lane, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]

theorem testBit_lane64 (N j i : ℕ) :
    (lane64 N j).testBit i = (decide (i < 64) && N.testBit (64 * j + i)) := by
  rw [lane64, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]

def LaneEq (N n j w : ℕ) : Prop := ∀ i < w, N.testBit (1280 * j + i) = n.testBit i

theorem LaneEq.xor {N n M m j w : ℕ} (h1 : LaneEq N n j w) (h2 : LaneEq M m j w) :
    LaneEq (N ^^^ M) (n ^^^ m) j w := fun i hi => by
  rw [Nat.testBit_xor, Nat.testBit_xor, h1 i hi, h2 i hi]

theorem LaneEq.and {N n M m j w : ℕ} (h1 : LaneEq N n j w) (h2 : LaneEq M m j w) :
    LaneEq (N &&& M) (n &&& m) j w := fun i hi => by
  rw [Nat.testBit_and, Nat.testBit_and, h1 i hi, h2 i hi]

theorem LaneEq.shr {N n j w s : ℕ} (h : LaneEq N n j (w + s)) :
    LaneEq (N >>> s) (n >>> s) j w := fun i hi => by
  rw [Nat.testBit_shiftRight, Nat.testBit_shiftRight, ← h (s + i) (by omega)]
  congr 1
  omega

theorem LaneEq.mono {N n j w w' : ℕ} (h : LaneEq N n j w) (hw : w' ≤ w) : LaneEq N n j w' :=
  fun i hi => h i (by omega)

theorem laneEq_lane (N j : ℕ) : LaneEq N (lane N j) j 1280 := fun i hi => by
  rw [testBit_lane]
  simp [hi]

theorem eq_of_laneEq {N n m j : ℕ} (h1 : LaneEq N n j 1280) (h2 : LaneEq N m j 1280)
    (hn : n < 2 ^ 1280) (hm : m < 2 ^ 1280) : n = m := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 1280
  · rw [← h1 i hi, h2 i hi]
  · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hn (Nat.pow_le_pow_right (by omega) (by omega))),
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hm (Nat.pow_le_pow_right (by omega) (by omega)))]

theorem lane_lt (N j : ℕ) : lane N j < 2 ^ 1280 := Nat.mod_lt _ (Nat.two_pow_pos _)

theorem lane_eq_of_laneEq {N n j : ℕ} (h : LaneEq N n j 1280) (hn : n < 2 ^ 1280) :
    lane N j = n :=
  eq_of_laneEq (laneEq_lane N j) h (lane_lt N j) hn

theorem testBit_stackN_s {s : ℕ} (hs : 0 < s) {F : ℕ → ℕ} (hF : ∀ k, F k < 2 ^ s) :
    ∀ m p, (stackN s m F).testBit p = (decide (p / s < m) && (F (p / s)).testBit (p % s))
  | 0, p => by simp [stackN]
  | m + 1, p => by
    have ih := testBit_stackN_s hs hF m p
    change (stackN s m F ||| F m <<< (s * m)).testBit p = _
    rw [Nat.testBit_or, ih, Nat.testBit_shiftLeft]
    have hq := Nat.div_add_mod p s
    have hr := Nat.mod_lt p hs
    by_cases h1 : p / s < m
    · have hge : ¬ (p ≥ s * m) := by
        intro h
        have : s * m ≤ s * (p / s) + p % s := by omega
        have h3 : s * (p / s) + p % s < s * m := by
          calc s * (p / s) + p % s < s * (p / s) + s := by omega
            _ = s * (p / s + 1) := by ring
            _ ≤ s * m := Nat.mul_le_mul_left _ h1
        omega
      have h3 : p / s < m + 1 := by omega
      simp [h1, hge, h3]
    · by_cases h2 : p / s = m
      · have hge : p ≥ s * m := by rw [← h2]; exact Nat.mul_div_le p s
        have e : p - s * m = p % s := by rw [← h2]; omega
        simp [h1, h2, hge, e]
      · have hm : m + 1 ≤ p / s := by omega
        have hge : p - s * m ≥ s := by
          have : s * (m + 1) ≤ s * (p / s) := Nat.mul_le_mul_left _ hm
          rw [Nat.mul_succ] at this
          omega
        have hz : (F m).testBit (p - s * m) = false :=
          Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (hF m) (Nat.pow_le_pow_right (by omega) hge))
        have hsm : p ≥ s * m := by
          have : s * m ≤ s * (p / s) := Nat.mul_le_mul_left _ (by omega)
          exact this.trans (Nat.mul_div_le p s)
        have h3 : ¬ p / s < m + 1 := by omega
        simp [h1, h2, hz, h3, hsm]

theorem testBit_stackN {F : ℕ → ℕ} (hF : ∀ k, F k < 2 ^ 1280) :
    ∀ m p, (stackN 1280 m F).testBit p = (decide (p / 1280 < m) && (F (p / 1280)).testBit (p % 1280)) :=
  testBit_stackN_s (by omega) hF

theorem lane_stackN {F : ℕ → ℕ} (hF : ∀ k, F k < 2 ^ 1280) {m j : ℕ} (hj : j < m) :
    lane (stackN 1280 m F) j = F j := by
  apply lane_eq_of_laneEq _ (hF j)
  intro i hi
  rw [testBit_stackN hF]
  have e1 : (1280 * j + i) / 1280 = j := by omega
  have e2 : (1280 * j + i) % 1280 = i := by omega
  simp [e1, e2, hj]

theorem lane_mulB {m j : ℕ} (hj : j < m) (S M : ℕ) :
    lane (mulB (rep 1 256 (5 * m)) (2 ^ 248 - 1) S M) j =
      mulB (rep 1 256 5) (2 ^ 248 - 1) (lane S j) M := by
  apply lane_eq_of_laneEq _ (Nat.lt_of_lt_of_le (mulB_lt 5 _ M) (by norm_num))
  intro i hi
  rw [testBit_mulB_rows, testBit_mulB_rows]
  have e1 : (1280 * j + i) % 256 = i % 256 := by omega
  have e2 : (1280 * j + i) / 256 = 5 * j + i / 256 := by omega
  rw [e1, e2]
  by_cases h : i % 256 < 248 ∧ i / 256 < 5
  · have h' : i % 256 < 248 ∧ 5 * j + i / 256 < 5 * m := ⟨h.1, by omega⟩
    simp only [h, h', and_self, decide_true, Bool.true_and]
    refine xsB_congr 248 fun k hk => ?_
    rw [testBit_lane]
    have e3 : 256 * (5 * j + i / 256) + k = 1280 * j + (256 * (i / 256) + k) := by ring
    rw [e3]
    have h3 : 256 * (i / 256) + k < 1280 := by omega
    simp [h3]
  · have h' : ¬ (i % 256 < 248 ∧ 5 * j + i / 256 < 5 * m) := by
      intro hh
      apply h
      exact ⟨hh.1, by omega⟩
    simp [h, h']

theorem m64_eq : m64 = 2 ^ 64 - 1 := rfl

theorem testBit_packD : ∀ (d Z p : ℕ),
    (packD d Z).testBit p = (decide (p / 64 < 2 ^ d) && Z.testBit (1280 * (p / 64) + p % 64))
  | 0, Z, p => by
    change (Z &&& m64).testBit p = _
    rw [Nat.testBit_and, m64_eq, Nat.testBit_two_pow_sub_one]
    by_cases h : p < 64
    · have e1 : p / 64 = 0 := by omega
      have e2 : p % 64 = p := by omega
      simp [h, e1, e2]
    · have : ¬ p / 64 < 2 ^ 0 := by simp; omega
      simp [h, this]
  | d + 1, Z, p => by
    change (packD d (Z &&& ((1 <<< (1280 * (1 <<< d))) - 1)) |||
      packD d (Z >>> (1280 * (1 <<< d))) <<< (64 * (1 <<< d))).testBit p = _
    rw [Nat.one_shiftLeft, Nat.one_shiftLeft]
    rw [Nat.testBit_or, Nat.testBit_shiftLeft, testBit_packD d, testBit_packD d]
    have hp2 : (2 : ℕ) ^ (d + 1) = 2 * 2 ^ d := by ring
    by_cases h1 : p / 64 < 2 ^ d
    · have hge : ¬ p ≥ 64 * 2 ^ d := by omega
      rw [Nat.testBit_and, Nat.testBit_two_pow_sub_one]
      have hlt : 1280 * (p / 64) + p % 64 < 1280 * 2 ^ d := by omega
      have h3 : p / 64 < 2 ^ (d + 1) := by omega
      simp [h1, hge, hlt, h3]
    · have hge : p ≥ 64 * 2 ^ d := by omega
      have e1 : (p - 64 * 2 ^ d) / 64 = p / 64 - 2 ^ d := by omega
      have e2 : (p - 64 * 2 ^ d) % 64 = p % 64 := by omega
      rw [e1, e2, Nat.testBit_shiftRight]
      have e3 : 1280 * 2 ^ d + (1280 * (p / 64 - 2 ^ d) + p % 64) = 1280 * (p / 64) + p % 64 := by
        have : 2 ^ d ≤ p / 64 := by omega
        rw [Nat.mul_sub]
        omega
      rw [e3]
      by_cases h2 : p / 64 < 2 ^ (d + 1)
      · have h3 : p / 64 - 2 ^ d < 2 ^ d := by omega
        simp [h1, hge, h2, h3]
      · have h3 : ¬ p / 64 - 2 ^ d < 2 ^ d := by omega
        simp [h1, hge, h2, h3]

theorem lane64_packD {d j : ℕ} (hj : j < 2 ^ d) (Z : ℕ) :
    lane64 (packD d Z) j = lane Z j % 2 ^ 64 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_lane64, Nat.testBit_mod_two_pow, testBit_lane, testBit_packD]
  by_cases hi : i < 64
  · have e1 : (64 * j + i) / 64 = j := by omega
    have e2 : (64 * j + i) % 64 = i := by omega
    have h3 : i < 1280 := by omega
    simp [hi, e1, e2, hj, h3]
  · simp [hi]

theorem keyAt_eq (K j : ℕ) : keyAt K j = lane64 K j := by
  unfold keyAt lane64
  have e : Nat.land (Nat.shiftRight K (Nat.mul 64 j)) m64 = (K >>> (64 * j)) &&& (2 ^ 64 - 1) := rfl
  rw [e,
    Nat.and_two_pow_sub_one_eq_mod]

theorem strictN_eq (y : ℕ) (k : ℕ → ℕ) : strictN y k = k y := by
  cases y <;> rfl

theorem rep_succ' (x s n : ℕ) : rep x s (n + 1) = rep x s n ||| x <<< (s * n) := rfl

theorem testBit_rep {x s : ℕ} (hs : 0 < s) (hx : x < 2 ^ s) :
    ∀ n p, (rep x s n).testBit p = (decide (p / s < n) && x.testBit (p % s))
  | 0, p => by simp [rep]
  | n + 1, p => by
    rw [rep_succ', Nat.testBit_or, testBit_rep hs hx n p, Nat.testBit_shiftLeft]
    by_cases h1 : p / s < n
    · have : ¬ p ≥ s * n := by
        intro h
        have := Nat.div_le_div_right (c := s) h
        rw [Nat.mul_div_cancel_left _ hs] at this
        omega
      have h3 : p / s < n + 1 := by omega
      simp [h1, this, h3]
    · by_cases h2 : p / s = n
      · have hge : p ≥ s * n := by
          rw [← h2]
          exact Nat.mul_div_le p s
        have e : p - s * n = p % s := by
          rw [← h2, Nat.mod_def]
        simp [h1, h2, hge, e]
      · have hge : p ≥ s * n := by
          have : n ≤ p / s := by omega
          calc s * n ≤ s * (p / s) := Nat.mul_le_mul_left _ this
            _ ≤ p := Nat.mul_div_le p s
        have hbig : p - s * n ≥ s := by
          have : n + 1 ≤ p / s := by omega
          have h3 : s * (n + 1) ≤ p := (Nat.mul_le_mul_left _ this).trans (Nat.mul_div_le p s)
          rw [Nat.mul_succ] at h3
          omega
        have hz : x.testBit (p - s * n) = false :=
          Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) hbig))
        have h3 : ¬ p / s < n + 1 := by omega
        simp [h1, h2, hge, hz, h3]

theorem div_lt_iff_lt_mul' {p s n : ℕ} (hs : 0 < s) : p / s < n ↔ p < s * n := by
  rw [Nat.div_lt_iff_lt_mul hs, Nat.mul_comm]

theorem testBit_repD {x s : ℕ} (hs : 0 < s) (hx : x < 2 ^ s) :
    ∀ d p, (repD x s d).testBit p = (decide (p / s < 2 ^ d) && x.testBit (p % s))
  | 0, p => by
    change x.testBit p = _
    by_cases h : p < s
    · rw [Nat.div_eq_of_lt h, Nat.mod_eq_of_lt h]
      simp
    · have hz : x.testBit p = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) (by omega)))
      have : ¬ p / s < 2 ^ 0 := by
        rw [div_lt_iff_lt_mul' hs]
        simpa using h
      rw [hz, decide_eq_false this, Bool.false_and]
  | d + 1, p => by
    change (repD x s d ||| repD x s d <<< (s * (1 <<< d))).testBit p = _
    rw [Nat.testBit_or, Nat.testBit_shiftLeft, testBit_repD hs hx d p, Nat.one_shiftLeft]
    by_cases h1 : p / s < 2 ^ d
    · have : ¬ p ≥ s * 2 ^ d := by
        rw [div_lt_iff_lt_mul' hs] at h1
        omega
      have hd : p / s < 2 ^ (d + 1) := by
        rw [Nat.pow_succ]
        omega
      simp [h1, this, hd]
    · have hge : p ≥ s * 2 ^ d := by
        rw [div_lt_iff_lt_mul' hs] at h1
        omega
      rw [testBit_repD hs hx d (p - s * 2 ^ d)]
      have hq : s * (p / s) + p % s = p := Nat.div_add_mod p s
      have hr : p % s < s := Nat.mod_lt p hs
      have hk : 2 ^ d ≤ p / s := by omega
      have hk' : s * 2 ^ d ≤ s * (p / s) := Nat.mul_le_mul_left s hk
      have e0 : p - s * 2 ^ d = p % s + s * (p / s - 2 ^ d) := by
        rw [Nat.mul_sub]
        omega
      have e1 : (p - s * 2 ^ d) / s = p / s - 2 ^ d := by
        rw [e0, Nat.add_mul_div_left _ _ hs, Nat.div_eq_of_lt hr, Nat.zero_add]
      have e2 : (p - s * 2 ^ d) % s = p % s := by
        rw [e0, Nat.add_mul_mod_self_left, Nat.mod_mod]
      rw [e1, e2]
      have hp : p / s - 2 ^ d < 2 ^ d ↔ p / s < 2 ^ (d + 1) := by
        rw [Nat.pow_succ]
        omega
      by_cases h3 : p / s < 2 ^ (d + 1)
      · simp [h1, hge, h3, hp.mpr h3]
      · have h4 : ¬ (p / s - 2 ^ d < 2 ^ d) := fun h => h3 (hp.mp h)
        simp [h1, hge, h3, h4]

theorem testBit_repN {x s d n : ℕ} (hs : 0 < s) (hx : x < 2 ^ s) (hn : n ≤ 2 ^ d) (p : ℕ) :
    (repN x s d n).testBit p = (decide (p / s < n) && x.testBit (p % s)) := by
  unfold repN
  have e : Nat.sub (Nat.shiftLeft 1 (Nat.mul s n)) 1 = 2 ^ (s * n) - 1 := by
    have e1 : Nat.shiftLeft 1 (Nat.mul s n) = 1 <<< (s * n) := rfl
    rw [e1, Nat.one_shiftLeft]
    rfl
  rw [e]
  change (repD x s d &&& (2 ^ (s * n) - 1)).testBit p = _
  rw [Nat.testBit_and, Nat.testBit_two_pow_sub_one, testBit_repD hs hx]
  by_cases h : p / s < n
  · have h' : p < s * n := (div_lt_iff_lt_mul' hs).mp h
    have h3 : p / s < 2 ^ d := by omega
    simp [h, h', h3]
  · have h' : ¬ p < s * n := fun hh => h ((div_lt_iff_lt_mul' hs).mpr hh)
    simp [h, h']

theorem laneEq_repN {x d m j : ℕ} (hx : x < 2 ^ 1280) (hm : m ≤ 2 ^ d) (hj : j < m) :
    LaneEq (repN x 1280 d m) x j 1280 := fun i hi => by
  rw [testBit_repN (by omega) hx hm]
  have e1 : (1280 * j + i) / 1280 = j := by omega
  have e2 : (1280 * j + i) % 1280 = i := by omega
  simp [e1, e2, hj]

theorem LaneEq.and_mask {N n L l j w : ℕ} (h : LaneEq N n j w) (hL : LaneEq L l j 1280)
    (hl : ∀ i, l.testBit i = true → i < w) (hw : w ≤ 1280) :
    LaneEq (N &&& L) (n &&& l) j 1280 := fun i hi => by
  rw [Nat.testBit_and, Nat.testBit_and, hL i hi]
  by_cases h2 : i < w
  · rw [h i h2]
  · have : l.testBit i = false := by
      cases e : l.testBit i
      · rfl
      · exact absurd (hl i e) h2
    simp [this]

theorem LaneEq.and5 {N n j w : ℕ} (h : LaneEq N n j (w + 4)) : LaneEq (and5 N) (and5 n) j w := by
  unfold CFSG.KC.ThDemp.and5
  refine LaneEq.and (LaneEq.and (LaneEq.and (LaneEq.and (h.mono (by omega)) ?_) ?_) ?_) ?_
  · exact LaneEq.shr (s := 1) (h.mono (by omega))
  · exact LaneEq.shr (s := 2) (h.mono (by omega))
  · exact LaneEq.shr (s := 3) (h.mono (by omega))
  · exact LaneEq.shr (s := 4) h

theorem LaneEq.subX {j w : ℕ} : ∀ (Bs bs : List ℕ), List.Forall₂ (fun B b => LaneEq B b j (w + 4)) Bs bs →
    ∀ (B b : ℕ), LaneEq B b j (w + 4) → LaneEq (subX Bs B) (subX bs b) j w
  | [], [], _, B, b, hb => LaneEq.and5 hb
  | B' :: Bs, b' :: bs, h, B, b, hb => by
    obtain ⟨h1, h2⟩ := List.forall₂_cons.mp h
    exact LaneEq.xor (LaneEq.subX Bs bs h2 B b hb) (LaneEq.subX Bs bs h2 _ _ (LaneEq.xor hb h1))

theorem m63_testBit (i : ℕ) : m63.testBit i = decide (i < 63) := by
  have e : m63 = 2 ^ 63 - 1 := rfl
  rw [e, Nat.testBit_two_pow_sub_one]

theorem m63_lt : m63 < 2 ^ 63 := by decide

theorem lane_keyB {d m j : ℕ} (hm : m ≤ 2 ^ d) (hj : j < m) (Z : ℕ) :
    lane (keyB (repN (2 ^ 248 - 1) 1280 d m) (repN m63 1280 d m) Z) j =
      keyL (2 ^ 248 - 1) (lane Z j) := by
  have hrm : (2 ^ 248 - 1 : ℕ) < 2 ^ 1280 :=
    Nat.lt_of_lt_of_le (Nat.sub_lt (Nat.two_pow_pos _) (by omega)) (Nat.pow_le_pow_right (by omega) (by omega))
  have h64 : m63 < 2 ^ 1280 :=
    Nat.lt_of_lt_of_le m63_lt (Nat.pow_le_pow_right (by omega) (by omega : 63 ≤ 1280))
  have hL := laneEq_repN hrm hm hj
  have hL64 := laneEq_repN (d := d) h64 hm hj
  have hlane : ∀ k : ℕ, k ≤ 4 → LaneEq ((Z >>> (256 * k)) &&& repN (2 ^ 248 - 1) 1280 d m)
      ((lane Z j >>> (256 * k)) &&& (2 ^ 248 - 1)) j 1280 := by
    intro k hk
    refine LaneEq.and_mask (w := 248) ?_ hL ?_ (by omega)
    · exact LaneEq.shr (s := 256 * k) ((laneEq_lane Z j).mono (by omega))
    · intro i hi
      rw [Nat.testBit_two_pow_sub_one] at hi
      simpa using hi
  unfold keyB keyL rowsOf
  simp only [strictN_eq]
  refine lane_eq_of_laneEq ?_ ?_
  · unfold fold64
    refine LaneEq.and_mask (w := 63) ?_ hL64 (fun i hi => by rw [m63_testBit] at hi; simpa using hi)
      (by omega)
    have hs := LaneEq.subX (j := j) (w := 1276)
      [(Z &&& repN (2 ^ 248 - 1) 1280 d m), ((Z >>> 256) &&& repN (2 ^ 248 - 1) 1280 d m),
        ((Z >>> 512) &&& repN (2 ^ 248 - 1) 1280 d m), ((Z >>> 768) &&& repN (2 ^ 248 - 1) 1280 d m),
        ((Z >>> 1024) &&& repN (2 ^ 248 - 1) 1280 d m)]
      [(lane Z j &&& (2 ^ 248 - 1)), ((lane Z j >>> 256) &&& (2 ^ 248 - 1)),
        ((lane Z j >>> 512) &&& (2 ^ 248 - 1)), ((lane Z j >>> 768) &&& (2 ^ 248 - 1)),
        ((lane Z j >>> 1024) &&& (2 ^ 248 - 1))]
      (by
        refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_
          (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ List.Forall₂.nil))))
        · simpa using hlane 0 (by omega)
        · simpa using hlane 1 (by omega)
        · simpa using hlane 2 (by omega)
        · simpa using hlane 3 (by omega)
        · simpa using hlane 4 (by omega))
      0 0 (fun i _ => by simp)
    have h1 := hs.mono (by omega : 63 + 192 ≤ 1276)
    refine LaneEq.xor (LaneEq.xor (h1.mono (by omega)) (LaneEq.shr (s := 64) (h1.mono (by omega))))
      (LaneEq.xor (LaneEq.shr (s := 128) (h1.mono (by omega))) (LaneEq.shr (s := 192) h1))
  · exact Nat.lt_of_lt_of_le (Nat.and_lt_two_pow _ m63_lt)
      (Nat.pow_le_pow_right (by omega) (by omega))

theorem keyL_lt (P : ℕ) : keyL (2 ^ 248 - 1) P < 2 ^ 63 := Nat.and_lt_two_pow _ m63_lt

end CFSG.Certificates.ThDemp.Lanes

end
