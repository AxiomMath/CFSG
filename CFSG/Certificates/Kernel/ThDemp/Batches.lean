module

public import CFSG.Certificates.Kernel.ThDemp.Lanes
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.Certificates.ThDemp.Batches

open CFSG.KC.Th CFSG.KC.Th.BigS CFSG.KC.ThDemp CFSG.KC.Loop CFSG.Certificates.ThDemp.Rows
  CFSG.Certificates.ThDemp.Lanes

set_option exponentiation.threshold 140000

variable {D : DempData} {O : OrbData}

theorem strictL_eq (y : ℕ) (k : ℕ → List ℕ) : strictL y k = k y := by
  cases y <;> rfl

theorem strictB_eq (y : ℕ) (k : ℕ → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem m1280_eq : m1280 = 2 ^ 1280 - 1 := by
  unfold m1280
  change Nat.sub (1 <<< 1280) 1 = 2 ^ 1280 - 1
  rw [Nat.one_shiftLeft]
  rfl

theorem ptAt_eq (S m : ℕ) : ptAt S m = lane S m := by
  unfold ptAt lane
  rw [m1280_eq]
  exact Nat.and_two_pow_sub_one_eq_mod _ _

theorem lget_eq (l : List ℕ) (i : ℕ) (h : i < l.length) : lget l i = l[i] := by
  induction l generalizing i with
  | nil => simp at h
  | cons a l ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih i (by simpa using h)

theorem lget_map_range (f : ℕ → ℕ) {n i : ℕ} (hi : i < n) : lget ((List.range n).map f) i = f i := by
  rw [lget_eq _ _ (by simpa using hi)]
  simp

theorem lane_stackN_mul {m q : ℕ} (hm : 0 < m) {F : ℕ → ℕ} (hF : ∀ k, F k < 2 ^ (1280 * m))
    {a b : ℕ} (ha : a < q) (hb : b < m) :
    lane (stackN (1280 * m) q F) (m * a + b) = lane (F a) b := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_lane, testBit_lane, testBit_stackN_s (by omega) hF]
  by_cases hi : i < 1280
  · have hlt : 1280 * b + i < 1280 * m := by
      have : 1280 * (b + 1) ≤ 1280 * m := Nat.mul_le_mul_left _ hb
      omega
    have e : 1280 * (m * a + b) + i = (1280 * b + i) + 1280 * m * a := by ring
    have e1 : (1280 * (m * a + b) + i) / (1280 * m) = a := by
      rw [e, Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hlt, Nat.zero_add]
    have e2 : (1280 * (m * a + b) + i) % (1280 * m) = 1280 * b + i := by
      rw [e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
    simp [hi, e1, e2, ha]
  · simp [hi]

theorem cR_eq (n : ℕ) : cR n = rep 1 256 n := rfl

theorem div512 {y3 r : ℕ} (hr : r < 512) : Nat.div (512 * y3 + r) 512 = y3 := by
  change (512 * y3 + r) / 512 = y3
  omega

theorem mod512 {y3 r : ℕ} (hr : r < 512) : Nat.mod (512 * y3 + r) 512 = r := by
  change (512 * y3 + r) % 512 = r
  omega

theorem testBit_mul_row {u : ℕ} (hu : ∀ q, u.testBit q = true → q % 256 = 0) :
    ∀ m, m ≤ 256 → ∀ v, v < 2 ^ m → ∀ p,
      (u * v).testBit p = (u.testBit (256 * (p / 256)) && v.testBit (p % 256))
  | 0, _, v, hv, p => by
    have : v = 0 := by simpa using hv
    subst this
    simp
  | m + 1, hm, v, hv, p => by
    have ih := testBit_mul_row hu m (by omega)
    by_cases hb : v < 2 ^ m
    · exact ih v hb p
    have hw : v % 2 ^ m < 2 ^ m := Nat.mod_lt _ (Nat.two_pow_pos m)
    have hv2 : v < 2 * 2 ^ m := by rw [Nat.pow_succ] at hv; omega
    have hmod : v % 2 ^ m = v - 2 ^ m := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    have hv' : v = v % 2 ^ m + 2 ^ m := by omega
    have hb2 : ∀ q, (u * 2 ^ m).testBit q = (decide (m ≤ q) && u.testBit (q - m)) := fun q => by
      rw [← Nat.shiftLeft_eq, Nat.testBit_shiftLeft]
    have hdis : (u * (v % 2 ^ m)) &&& (u * 2 ^ m) = 0 := by
      apply Nat.eq_of_testBit_eq
      intro q
      rw [Nat.testBit_and, ih _ hw, hb2, Nat.zero_testBit, Bool.eq_false_iff]
      intro hq
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hq
      obtain ⟨⟨-, h2⟩, h3, h4⟩ := hq
      have := hu _ h4
      have e : q % 256 = m := by omega
      rw [e, Nat.testBit_lt_two_pow hw] at h2
      exact absurd h2 (by decide)
    rw [hv', Nat.mul_add, add_eq_or_of_land_eq_zero _ _ hdis, Nat.testBit_or, ih _ hw, hb2,
      ← Nat.or_two_pow_eq_add_of_lt hw, Nat.testBit_or, Nat.testBit_two_pow]
    by_cases h : m = p % 256
    · subst h
      have e : p - p % 256 = 256 * (p / 256) := by omega
      have hm' : p % 256 ≤ p := Nat.mod_le _ _
      have hW : (v % 2 ^ (p % 256)).testBit (p % 256) = false := Nat.testBit_lt_two_pow hw
      simp [e, hm', hW]
    · have h2 : (decide (m ≤ p) && u.testBit (p - m)) = false := by
        rw [Bool.eq_false_iff]
        intro hq
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hq
        have := hu _ hq.2
        omega
      rw [h2]
      simp [h]

theorem stepCol_eq (n A B k : ℕ) :
    ((A >>> k) &&& rep 1 256 n) * ((B >>> (k * 256)) &&& (2 ^ 248 - 1)) =
      stepP (rep 1 256 n) (2 ^ 248 - 1) A B k := by
  apply Nat.eq_of_testBit_eq
  intro p
  have hu : ∀ q, ((A >>> k) &&& rep 1 256 n).testBit q = true → q % 256 = 0 := by
    intro q hq
    rw [Nat.testBit_and, testBit_cn, Bool.and_eq_true, decide_eq_true_eq] at hq
    exact hq.2.1
  have hv : ((B >>> (k * 256)) &&& (2 ^ 248 - 1)) < 2 ^ 256 :=
    Nat.lt_of_lt_of_le (Nat.and_lt_two_pow _ (Nat.sub_lt (Nat.two_pow_pos _) (by omega)))
      (Nat.pow_le_pow_right (by omega) (by omega))
  rw [testBit_stepP, testBit_mul_row hu 256 le_rfl _ hv p, Nat.testBit_and, Nat.testBit_and,
    Nat.testBit_shiftRight, Nat.testBit_shiftRight, testBit_cn, Nat.testBit_two_pow_sub_one]
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  have e1 : 256 * (p / 256) % 256 = 0 := by omega
  have e2 : 256 * (p / 256) / 256 = p / 256 := by omega
  rw [e1, e2, Nat.add_comm k, Nat.mul_comm k]
  simp only [true_and]
  tauto

@[expose] noncomputable def mulColn (c rm A B m : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0 (fun k acc => Nat.xor acc (Nat.mul (Nat.land (Nat.shiftRight A k) c)
    (Nat.land (Nat.shiftRight B (Nat.mul k 256)) rm))) m

theorem mulColn_eq (n A B : ℕ) : ∀ m,
    mulColn (rep 1 256 n) (2 ^ 248 - 1) A B m = mulBn (rep 1 256 n) (2 ^ 248 - 1) A B m
  | 0 => rfl
  | m + 1 => by
    rw [mulBn_succ, ← stepCol_eq, ← mulColn_eq n A B m]
    rfl

theorem mulCol_eq (n A B : ℕ) :
    mulCol (rep 1 256 n) (2 ^ 248 - 1) A B = mulB (rep 1 256 n) (2 ^ 248 - 1) A B :=
  (mulColn_eq n A B 248).trans (mulB_eq_mulBn _ _ _ _).symm

variable (hrm : D.rm = 2 ^ 248 - 1)
include hrm

theorem xBat_get (P : ℕ) {y3 : ℕ} (h3 : y3 < 24) :
    lget (xBat D P) y3 = mulB (rep 1 256 (5 * 512)) (2 ^ 248 - 1) (xS4 D P) (D.T 3 y3) := by
  unfold xBat
  rw [strictL_eq, strictL_eq, lget_map_range _ h3, hrm, cR_eq]
  exact mulCol_eq _ _ _

theorem yBat_get (P : ℕ) {y2 : ℕ} (h2 : y2 < 28) :
    lget (yBat D O P) y2 = mulB (rep 1 256 (5 * 930)) (2 ^ 248 - 1)
      (stackN (1280 * 31) 30 (fun y1 => mulB (rep 1 256 (5 * 31)) (2 ^ 248 - 1)
        (stackN 1280 31 (fun y0 => mulB (rep 1 256 5) (2 ^ 248 - 1) P (O.TI 0 y0))) (O.TI 1 y1)))
      (O.TI 2 y2) := by
  unfold yBat
  simp only [strictL_eq]
  rw [lget_map_range _ h2, hrm]
  simp only [cR_eq, mulCol_eq]

theorem lane_xS4 (P : ℕ) {y4 y5 : ℕ} (h4 : y4 < 16) (h5 : y5 < 32) :
    lane (xS4 D P) (32 * y4 + y5) =
      mulB (rep 1 256 5) (2 ^ 248 - 1) (mulB (rep 1 256 5) (2 ^ 248 - 1) P (D.T 5 y5)) (D.T 4 y4) := by
  have e : xS4 D P = stackN (1280 * 32) 16 (fun y4 => mulB (rep 1 256 (5 * 32)) (2 ^ 248 - 1)
      (stackN 1280 32 (fun y5 => mulB (rep 1 256 5) (2 ^ 248 - 1) P (D.T 5 y5))) (D.T 4 y4)) := by
    unfold xS4
    rw [strictN_eq, hrm]
    simp only [cR_eq, mulCol_eq]
  rw [e, lane_stackN_mul (by omega) (fun k => mulB_lt (5 * 32) _ _) h4 h5, lane_mulB h5,
    lane_stackN (fun k => Nat.lt_of_lt_of_le (mulB_lt 5 _ _) (by norm_num)) h5]

theorem xPt_xBat (P : ℕ) {y3 y4 y5 : ℕ} (h3 : y3 < 24) (h4 : y4 < 16) (h5 : y5 < 32) :
    xPt (xBat D P) (512 * y3 + (32 * y4 + y5)) =
      mulB (rep 1 256 5) (2 ^ 248 - 1) (mulB (rep 1 256 5) (2 ^ 248 - 1)
        (mulB (rep 1 256 5) (2 ^ 248 - 1) P (D.T 5 y5)) (D.T 4 y4)) (D.T 3 y3) := by
  unfold xPt
  rw [div512 (by omega), mod512 (by omega), xBat_get hrm P h3, ptAt_eq, lane_mulB (by omega),
    lane_xS4 hrm P h4 h5]

theorem yPt_yBat (P : ℕ) {y0 y1 y2 : ℕ} (h0 : y0 < 31) (h1 : y1 < 30) (h2 : y2 < 28) :
    yPt (yBat D O P) (930 * y2 + (31 * y1 + y0)) =
      mulB (rep 1 256 5) (2 ^ 248 - 1) (mulB (rep 1 256 5) (2 ^ 248 - 1)
        (mulB (rep 1 256 5) (2 ^ 248 - 1) P (O.TI 0 y0)) (O.TI 1 y1)) (O.TI 2 y2) := by
  unfold yPt
  have e1 : Nat.div (930 * y2 + (31 * y1 + y0)) 930 = y2 := by
    change (930 * y2 + (31 * y1 + y0)) / 930 = y2
    omega
  have e2 : Nat.mod (930 * y2 + (31 * y1 + y0)) 930 = 31 * y1 + y0 := by
    change (930 * y2 + (31 * y1 + y0)) % 930 = 31 * y1 + y0
    omega
  rw [e1, e2, yBat_get hrm P h2, ptAt_eq, lane_mulB (by omega),
    lane_stackN_mul (by omega) (fun k => mulB_lt (5 * 31) _ _) h1 h0, lane_mulB h0,
    lane_stackN (fun k => Nat.lt_of_lt_of_le (mulB_lt 5 _ _) (by norm_num)) h0]

theorem keyAt_xKeys (P : ℕ) {y3 p : ℕ} (h3 : y3 < 24) (hp : p < 512) :
    keyAt (xKeys D P y3) p = keyL (2 ^ 248 - 1) (xPt (xBat D P) (512 * y3 + p)) := by
  have e : xPt (xBat D P) (512 * y3 + p) =
      lane (mulB (rep 1 256 (5 * 512)) (2 ^ 248 - 1) (xS4 D P) (D.T 3 y3)) p := by
    unfold xPt
    rw [div512 hp, mod512 hp, xBat_get hrm P h3, ptAt_eq]
  rw [e, keyAt_eq]
  unfold xKeys
  rw [hrm, lane64_packD (lt_of_lt_of_eq hp (by norm_num)), cR_eq, lane_keyB (by norm_num) hp]
  exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (keyL_lt _) (by norm_num))

omit hrm in
theorem testBit_keyB_high {d n : ℕ} (hn : n ≤ 2 ^ d) (Z i : ℕ) (hi : 1280 * n ≤ i) :
    (keyB (repN (2 ^ 248 - 1) 1280 d n) (repN m63 1280 d n) Z).testBit i = false := by
  unfold keyB fold64
  simp only [strictN_eq]
  change (_ &&& repN m63 1280 d n).testBit i = false
  rw [Nat.testBit_and, testBit_repN (by omega)
    (Nat.lt_of_lt_of_le m63_lt (Nat.pow_le_pow_right (by omega) (by omega))) hn]
  have : ¬ i / 1280 < n := by omega
  simp [this]

omit hrm in
theorem packD_lt {d n : ℕ} (_hn : n ≤ 2 ^ d) {Z : ℕ} (hZ : ∀ i, 1280 * n ≤ i → Z.testBit i = false) :
    packD d Z < 2 ^ (64 * n) := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  rw [testBit_packD]
  by_cases h : i / 64 < 2 ^ d
  · rw [hZ _ (by omega)]
    simp
  · simp [h]

omit hrm in
theorem testBit_packE : ∀ (d Z p : ℕ),
    (packE d Z).testBit p = (decide (p / 64 < 2 ^ d) && Z.testBit (256 * (p / 64) + p % 64))
  | 0, Z, p => by
    change (Z &&& m64).testBit p = _
    rw [Nat.testBit_and, m64_eq, Nat.testBit_two_pow_sub_one]
    by_cases h : p < 64
    · have e1 : p / 64 = 0 := by omega
      have e2 : p % 64 = p := by omega
      simp [h, e1, e2]
    · simp [h]
  | d + 1, Z, p => by
    change (packE d (Z &&& ((1 <<< (256 * (1 <<< d))) - 1)) |||
      packE d (Z >>> (256 * (1 <<< d))) <<< (64 * (1 <<< d))).testBit p = _
    rw [Nat.one_shiftLeft, Nat.one_shiftLeft]
    rw [Nat.testBit_or, Nat.testBit_shiftLeft, testBit_packE d, testBit_packE d]
    have hp2 : (2 : ℕ) ^ (d + 1) = 2 * 2 ^ d := by ring
    by_cases h1 : p / 64 < 2 ^ d
    · have hge : ¬ p ≥ 64 * 2 ^ d := by omega
      rw [Nat.testBit_and, Nat.testBit_two_pow_sub_one]
      have hlt : 256 * (p / 64) + p % 64 < 256 * 2 ^ d := by omega
      have h3 : p / 64 < 2 ^ (d + 1) := by omega
      simp [h1, hge, hlt, h3]
    · have hge : p ≥ 64 * 2 ^ d := by omega
      have e1 : (p - 64 * 2 ^ d) / 64 = p / 64 - 2 ^ d := by omega
      have e2 : (p - 64 * 2 ^ d) % 64 = p % 64 := by omega
      rw [e1, e2, Nat.testBit_shiftRight]
      have e3 : 256 * 2 ^ d + (256 * (p / 64 - 2 ^ d) + p % 64) = 256 * (p / 64) + p % 64 := by
        have : 2 ^ d ≤ p / 64 := by omega
        rw [Nat.mul_sub]
        omega
      rw [e3]
      by_cases h2 : p / 64 < 2 ^ (d + 1)
      · have h3 : p / 64 - 2 ^ d < 2 ^ d := by omega
        simp [h1, hge, h2, h3]
      · have h3 : ¬ p / 64 - 2 ^ d < 2 ^ d := by omega
        simp [h1, hge, h2, h3]

def LaneQ (N n j w : ℕ) : Prop := ∀ i < w, N.testBit (256 * j + i) = n.testBit i

omit hrm in
theorem LaneQ.xor {N n M m j w : ℕ} (h1 : LaneQ N n j w) (h2 : LaneQ M m j w) :
    LaneQ (N ^^^ M) (n ^^^ m) j w := fun i hi => by
  rw [Nat.testBit_xor, Nat.testBit_xor, h1 i hi, h2 i hi]

omit hrm in
theorem LaneQ.and {N n M m j w : ℕ} (h1 : LaneQ N n j w) (h2 : LaneQ M m j w) :
    LaneQ (N &&& M) (n &&& m) j w := fun i hi => by
  rw [Nat.testBit_and, Nat.testBit_and, h1 i hi, h2 i hi]

omit hrm in
theorem LaneQ.shr {N n j w s : ℕ} (h : LaneQ N n j (w + s)) :
    LaneQ (N >>> s) (n >>> s) j w := fun i hi => by
  rw [Nat.testBit_shiftRight, Nat.testBit_shiftRight, ← h (s + i) (by omega)]
  congr 1
  omega

omit hrm in
theorem LaneQ.mono {N n j w w' : ℕ} (h : LaneQ N n j w) (hw : w' ≤ w) : LaneQ N n j w' :=
  fun i hi => h i (by omega)

omit hrm in
theorem and5_eq (v : ℕ) : and5 v = v &&& (v >>> 1) &&& (v >>> 2) &&& (v >>> 3) &&& (v >>> 4) := rfl

omit hrm in
theorem and5_lt {n : ℕ} (hn : n < 2 ^ 248) : and5 n < 2 ^ 248 := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  rw [and5_eq]
  simp [Nat.testBit_and, Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hn (Nat.pow_le_pow_right (by omega) hi))]

omit hrm in
theorem LaneQ.and5 {N n j : ℕ} (h : LaneQ N n j 256) (hn : n < 2 ^ 248) :
    LaneQ (CFSG.KC.ThDemp.and5 N) (CFSG.KC.ThDemp.and5 n) j 256 := by
  have h252 : LaneQ (CFSG.KC.ThDemp.and5 N) (CFSG.KC.ThDemp.and5 n) j 252 := by
    rw [and5_eq, and5_eq]
    refine LaneQ.and (LaneQ.and (LaneQ.and (LaneQ.and (h.mono (by omega)) ?_) ?_) ?_) ?_
    · exact LaneQ.shr (s := 1) (h.mono (by omega))
    · exact LaneQ.shr (s := 2) (h.mono (by omega))
    · exact LaneQ.shr (s := 3) (h.mono (by omega))
    · exact LaneQ.shr (s := 4) (h.mono (by omega))
  intro i hi
  by_cases h2 : i < 252
  · exact h252 i h2
  · have hz : n.testBit i = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hn (Nat.pow_le_pow_right (by omega) (by omega)))
    have hz' : N.testBit (256 * j + i) = false := by rw [h i hi, hz]
    rw [and5_eq, and5_eq]
    simp [Nat.testBit_and, hz, hz']

omit hrm in
theorem LaneQ.subX {j : ℕ} : ∀ (Bs bs : List ℕ),
    List.Forall₂ (fun B b => LaneQ B b j 256 ∧ b < 2 ^ 248) Bs bs →
    ∀ (B b : ℕ), LaneQ B b j 256 → b < 2 ^ 248 → LaneQ (subX Bs B) (subX bs b) j 256
  | [], [], _, B, b, hB, hb => LaneQ.and5 hB hb
  | B' :: Bs, b' :: bs, h, B, b, hB, hb => by
    obtain ⟨⟨h1, h1'⟩, h2⟩ := List.forall₂_cons.mp h
    exact LaneQ.xor (LaneQ.subX Bs bs h2 B b hB hb)
      (LaneQ.subX Bs bs h2 _ _ (LaneQ.xor hB h1) (Nat.xor_lt_two_pow hb h1'))

omit hrm in
theorem testBit_keyD {d m j : ℕ} (hm : m ≤ 2 ^ d) (hj : j < m) (b : ℕ → ℕ) (Q : ℕ)
    (hb : ∀ k < 5, LaneQ (b k) ((Q >>> (256 * k)) &&& (2 ^ 248 - 1)) j 256) {i : ℕ} (hi : i < 64) :
    (fold64 (repN m63 256 d m) (subX [b 0, b 1, b 2, b 3, b 4] 0)).testBit (256 * j + i) =
      (keyL (2 ^ 248 - 1) Q).testBit i := by
  have hlt : ∀ k, (Q >>> (256 * k)) &&& (2 ^ 248 - 1) < 2 ^ 248 := fun k =>
    Nat.and_lt_two_pow _ (Nat.sub_lt (Nat.two_pow_pos _) (by omega))
  have hs := LaneQ.subX (j := j) [b 0, b 1, b 2, b 3, b 4] (rowsOf (2 ^ 248 - 1) Q)
    (by
      refine List.Forall₂.cons ⟨?_, hlt 0⟩ (List.Forall₂.cons ⟨?_, hlt 1⟩ (List.Forall₂.cons ⟨?_, hlt 2⟩
        (List.Forall₂.cons ⟨?_, hlt 3⟩ (List.Forall₂.cons ⟨?_, hlt 4⟩ List.Forall₂.nil))))
      · simpa using hb 0 (by omega)
      · exact hb 1 (by omega)
      · exact hb 2 (by omega)
      · exact hb 3 (by omega)
      · exact hb 4 (by omega))
    0 0 (fun i _ => by simp) (by norm_num)
  have h1 := hs.mono (by omega : 63 + 192 ≤ 256)
  have hx : LaneQ (fold64 (repN m63 256 d m) (subX [b 0, b 1, b 2, b 3, b 4] 0))
      (keyL (2 ^ 248 - 1) Q) j 63 := by
    unfold keyL fold64
    intro i hi
    have hm63 : (repN m63 256 d m).testBit (256 * j + i) = m63.testBit i := by
      rw [testBit_repN (by omega) (Nat.lt_of_lt_of_le m63_lt (Nat.pow_le_pow_right (by omega) (by omega))) hm]
      have e1 : (256 * j + i) / 256 = j := by omega
      have e2 : (256 * j + i) % 256 = i := by omega
      simp [e1, e2, hj]
    change Nat.testBit (_ &&& _ : ℕ) _ = Nat.testBit (_ &&& _ : ℕ) _
    rw [Nat.testBit_and, Nat.testBit_and, hm63]
    congr 1
    exact (LaneQ.xor (LaneQ.xor (h1.mono (by omega)) (LaneQ.shr (s := 64) (h1.mono (by omega))))
      (LaneQ.xor (LaneQ.shr (s := 128) (h1.mono (by omega))) (LaneQ.shr (s := 192) h1))) i hi
  by_cases h63 : i < 63
  · exact hx i h63
  · have hz : (keyL (2 ^ 248 - 1) Q).testBit i = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (keyL_lt Q) (Nat.pow_le_pow_right (by omega) (by omega)))
    rw [hz]
    unfold fold64
    change Nat.testBit (_ &&& _ : ℕ) _ = _
    rw [Nat.testBit_and, testBit_repN (by omega)
      (Nat.lt_of_lt_of_le m63_lt (Nat.pow_le_pow_right (by omega) (by omega))) hm, m63_testBit]
    have e2 : (256 * j + i) % 256 = i := by omega
    simp [e2, h63]

omit hrm in
theorem testBit_fold64_high {d m : ℕ} (hm : m ≤ 2 ^ d) (X i : ℕ) (hi : 256 * m ≤ i) :
    (fold64 (repN m63 256 d m) X).testBit i = false := by
  unfold fold64
  change (_ &&& repN m63 256 d m).testBit i = false
  rw [Nat.testBit_and, testBit_repN (by omega)
    (Nat.lt_of_lt_of_le m63_lt (Nat.pow_le_pow_right (by omega) (by omega))) hm]
  have : ¬ i / 256 < m := by omega
  simp [this]

omit hrm in
theorem laneQ_mulB {n r : ℕ} (A B : ℕ) :
    LaneQ (mulB (rep 1 256 n) (2 ^ 248 - 1) A B)
      ((mulB (rep 1 256 n) (2 ^ 248 - 1) A B >>> (256 * r)) &&& (2 ^ 248 - 1)) r 256 := fun i hi => by
  rw [Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one]
  by_cases h : i < 248
  · simp [h]
  · rw [testBit_mulB_rows]
    have e : (256 * r + i) % 256 = i := by omega
    simp [e, h]

omit hrm in
theorem row_stackN_mul {m q s : ℕ} (hs : s = 256 * m) (hm : 0 < m) {F : ℕ → ℕ} (hF : ∀ k, F k < 2 ^ s)
    {a b : ℕ} (ha : a < q) (hb : b < m) :
    (stackN s q F >>> (256 * (m * a + b))) &&& (2 ^ 248 - 1) = (F a >>> (256 * b)) &&& (2 ^ 248 - 1) := by
  subst hs
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_shiftRight,
    Nat.testBit_two_pow_sub_one, testBit_stackN_s (by omega) hF]
  by_cases hi : i < 248
  · have hlt : 256 * b + i < 256 * m := by
      have : 256 * (b + 1) ≤ 256 * m := Nat.mul_le_mul_left _ hb
      omega
    have e : 256 * (m * a + b) + i = (256 * b + i) + 256 * m * a := by ring
    have e1 : (256 * (m * a + b) + i) / (256 * m) = a := by
      rw [e, Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hlt, Nat.zero_add]
    have e2 : (256 * (m * a + b) + i) % (256 * m) = 256 * b + i := by
      rw [e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
    simp [hi, e1, e2, ha]
  · simp [hi]

omit hrm in
theorem row_window {S a b w : ℕ} (hb : 256 * b + 248 ≤ w) :
    (((S >>> a) &&& ((1 <<< w) - 1)) >>> (256 * b)) &&& (2 ^ 248 - 1) =
      (S >>> (a + 256 * b)) &&& (2 ^ 248 - 1) := by
  rw [Nat.shiftLeft_eq, Nat.one_mul]
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one]
  by_cases hi : i < 248
  · have hw : 256 * b + i < w := by omega
    simp [hi, hw, Nat.add_assoc]
  · simp [hi]

omit hrm in
theorem window_lt (x w : ℕ) : x &&& ((1 <<< w) - 1) < 2 ^ w :=
  Nat.and_lt_two_pow _ (by rw [Nat.shiftLeft_eq, Nat.one_mul]; exact Nat.sub_one_lt (Nat.two_pow_pos w).ne')

theorem row_yRowK (P : ℕ) {k y0 y1 : ℕ} (hk : k < 5) (h0 : y0 < 31) (h1 : y1 < 30) :
    (yRowK D O P k >>> (256 * (31 * y1 + y0))) &&& (2 ^ 248 - 1) =
      vecB (2 ^ 248 - 1) (vecB (2 ^ 248 - 1) ((P >>> (256 * k)) &&& (2 ^ 248 - 1)) (O.TI 0 y0))
        (O.TI 1 y1) := by
  unfold yRowK yS1
  simp only [strictN_eq]
  rw [hrm]
  simp only [cR_eq, mulCol_eq]
  set Q := stackN 1280 31 (fun y0 => mulB (rep 1 256 5) (2 ^ 248 - 1) P (O.TI 0 y0)) with hQ
  set S0 := stackN 256 155 (fun j => (Q >>> (1280 * (j % 31) + 256 * (j / 31))) &&& (2 ^ 248 - 1))
    with hS0
  set S := stackN 39680 30 (fun y1 => mulB (rep 1 256 155) (2 ^ 248 - 1) S0 (O.TI 1 y1)) with hS
  change (stackN 7936 30 (fun y1 => (S >>> (39680 * y1 + 7936 * k)) &&& ((1 <<< 7936) - 1)) >>>
    (256 * (31 * y1 + y0))) &&& (2 ^ 248 - 1) = _
  rw [row_stackN_mul (m := 31) (by norm_num) (by omega) (fun _ => window_lt _ _) h1 h0,
    row_window (by omega)]
  have e : 39680 * y1 + 7936 * k + 256 * y0 = 256 * (155 * y1 + (31 * k + y0)) := by ring
  rw [e, hS, row_stackN_mul (m := 155) (by norm_num) (by omega) (fun _ => mulB_lt 155 _ _) h1
    (by omega), row_mulB (by omega)]
  congr 1
  have e2 := row_stackN_mul (m := 1) (q := 155) (s := 256) (b := 0) (by norm_num) (by omega)
    (F := fun j => (Q >>> (1280 * (j % 31) + 256 * (j / 31))) &&& (2 ^ 248 - 1))
    (fun _ => Nat.and_lt_two_pow _ (lt_of_lt_of_le (Nat.sub_one_lt (Nat.two_pow_pos 248).ne')
      (Nat.pow_le_pow_right (by norm_num) (by norm_num))))
    (a := 31 * k + y0) (by omega) (by omega)
  simp only [Nat.one_mul, Nat.add_zero, Nat.mul_zero, Nat.shiftRight_zero] at e2
  rw [hS0, e2, Nat.and_assoc, Nat.and_self]
  have em : (31 * k + y0) % 31 = y0 := by omega
  have ed : (31 * k + y0) / 31 = k := by omega
  have e3 : 1280 * y0 + 256 * k = 256 * (5 * y0 + k) := by ring
  rw [em, ed, e3, hQ, row_stackN_mul (m := 5) (by norm_num) (by omega) (fun _ => mulB_lt 5 _ _) h0 hk,
    row_mulB hk]

theorem laneQ_yRow (P : ℕ) {k y0 y1 y2 : ℕ} (hk : k < 5) (h0 : y0 < 31) (h1 : y1 < 30)
    (h2 : y2 < 28) :
    LaneQ (mulB (rep 1 256 930) (2 ^ 248 - 1) (yRowK D O P k) (O.TI 2 y2))
      ((yPt (yBat D O P) (930 * y2 + (31 * y1 + y0)) >>> (256 * k)) &&& (2 ^ 248 - 1))
      (31 * y1 + y0) 256 := by
  have e : (yPt (yBat D O P) (930 * y2 + (31 * y1 + y0)) >>> (256 * k)) &&& (2 ^ 248 - 1) =
      (mulB (rep 1 256 930) (2 ^ 248 - 1) (yRowK D O P k) (O.TI 2 y2) >>> (256 * (31 * y1 + y0))) &&&
        (2 ^ 248 - 1) := by
    rw [yPt_yBat hrm P h0 h1 h2, row_mulB hk, row_mulB hk, row_mulB hk, row_mulB (by omega),
      row_yRowK hrm P hk h0 h1]
  rw [e]
  exact laneQ_mulB _ _

theorem keyAt_yKeysD (P : ℕ) {y : ℕ} (hy : y < 26040) :
    keyAt (yKeysD D O P) y = keyL (2 ^ 248 - 1) (yPt (yBat D O P) y) := by
  rw [keyAt_eq]
  unfold yKeysD
  simp only [strictN_eq]
  rw [hrm]
  simp only [cR_eq, mulCol_eq]
  set K : ℕ → ℕ := fun y2 => packE 10 (fold64 (repN m63 256 10 930)
    (subX [mulB (rep 1 256 930) (2 ^ 248 - 1) (yRowK D O P 0) (O.TI 2 y2),
      mulB (rep 1 256 930) (2 ^ 248 - 1) (yRowK D O P 1) (O.TI 2 y2),
      mulB (rep 1 256 930) (2 ^ 248 - 1) (yRowK D O P 2) (O.TI 2 y2),
      mulB (rep 1 256 930) (2 ^ 248 - 1) (yRowK D O P 3) (O.TI 2 y2),
      mulB (rep 1 256 930) (2 ^ 248 - 1) (yRowK D O P 4) (O.TI 2 y2)] 0)) with hK
  have hF : ∀ k, K k < 2 ^ 59520 := fun k => by
    apply Nat.lt_pow_two_of_testBit
    intro i hi
    rw [hK, testBit_packE]
    by_cases h : i / 64 < 2 ^ 10
    · rw [testBit_fold64_high (d := 10) (by norm_num) _ _ (by omega)]
      simp
    · rw [decide_eq_false h, Bool.false_and]
  have hy3 : y / 930 < 28 := by omega
  have hr : y % 930 < 930 := by omega
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_lane64, testBit_stackN_s (by omega) hF]
  by_cases hi : i < 64
  · have e1 : (64 * y + i) / 59520 = y / 930 := by omega
    have e2 : (64 * y + i) % 59520 = 64 * (y % 930) + i := by omega
    rw [e1, e2, hK, testBit_packE]
    have e3 : (64 * (y % 930) + i) / 64 = y % 930 := by omega
    have e4 : (64 * (y % 930) + i) % 64 = i := by omega
    rw [e3, e4]
    have hyd : y = 930 * (y / 930) + (31 * (y % 930 / 31) + y % 930 % 31) := by omega
    have hkey := testBit_keyD (d := 10) (m := 930) (by norm_num) hr
      (fun k => mulB (rep 1 256 930) (2 ^ 248 - 1) (yRowK D O P k) (O.TI 2 (y / 930)))
      (yPt (yBat D O P) y) (fun k hk => by
        have h := laneQ_yRow hrm (O := O) P hk (Nat.mod_lt (y % 930) (by omega))
          (by omega : y % 930 / 31 < 30) hy3
        have e5 : 31 * (y % 930 / 31) + y % 930 % 31 = y % 930 := by omega
        rw [e5, Nat.div_add_mod] at h
        exact h) hi
    simp only [hy3, hi, decide_true, Bool.true_and, (by omega : y % 930 < 2 ^ 10)]
    exact hkey
  · simp only [hi, decide_false, Bool.false_and]
    exact (Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (keyL_lt _)
      (Nat.pow_le_pow_right (by omega) (by omega)))).symm

end CFSG.Certificates.ThDemp.Batches

end
