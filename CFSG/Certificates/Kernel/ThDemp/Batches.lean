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

variable (hrm : D.rm = 2 ^ 248 - 1)
include hrm

theorem xBat_get (P : ℕ) {y3 : ℕ} (h3 : y3 < 24) :
    lget (xBat D P) y3 = mulB (rep 1 256 (5 * 512)) (2 ^ 248 - 1) (xS4 D P) (D.T 3 y3) := by
  unfold xBat
  rw [strictL_eq, strictL_eq, lget_map_range _ h3, hrm, cR_eq]

theorem yBat_get (P : ℕ) {y2 : ℕ} (h2 : y2 < 28) :
    lget (yBat D O P) y2 = mulB (rep 1 256 (5 * 930)) (2 ^ 248 - 1)
      (stackN (1280 * 31) 30 (fun y1 => mulB (rep 1 256 (5 * 31)) (2 ^ 248 - 1)
        (stackN 1280 31 (fun y0 => mulB (rep 1 256 5) (2 ^ 248 - 1) P (O.TI 0 y0))) (O.TI 1 y1)))
      (O.TI 2 y2) := by
  unfold yBat
  simp only [strictL_eq]
  rw [lget_map_range _ h2, hrm]
  rfl

theorem lane_xS4 (P : ℕ) {y4 y5 : ℕ} (h4 : y4 < 16) (h5 : y5 < 32) :
    lane (xS4 D P) (32 * y4 + y5) =
      mulB (rep 1 256 5) (2 ^ 248 - 1) (mulB (rep 1 256 5) (2 ^ 248 - 1) P (D.T 5 y5)) (D.T 4 y4) := by
  have e : xS4 D P = stackN (1280 * 32) 16 (fun y4 => mulB (rep 1 256 (5 * 32)) (2 ^ 248 - 1)
      (stackN 1280 32 (fun y5 => mulB (rep 1 256 5) (2 ^ 248 - 1) P (D.T 5 y5))) (D.T 4 y4)) := by
    unfold xS4
    rw [strictN_eq, hrm]
    rfl
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
theorem packD_lt {d n : ℕ} (hn : n ≤ 2 ^ d) {Z : ℕ} (hZ : ∀ i, 1280 * n ≤ i → Z.testBit i = false) :
    packD d Z < 2 ^ (64 * n) := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  rw [testBit_packD]
  by_cases h : i / 64 < 2 ^ d
  · rw [hZ _ (by omega)]
    simp
  · simp [h]

theorem keyAt_yKeys (W : List ℕ) {y : ℕ} (hy : y < 26040) :
    keyAt (yKeys D W) y = keyL (2 ^ 248 - 1) (yPt W y) := by
  rw [keyAt_eq]
  unfold yKeys yPt
  rw [hrm, strictN_eq, strictN_eq, ptAt_eq]
  have hF : ∀ k, packD 10 (keyB (repN (2 ^ 248 - 1) 1280 10 930) (repN m63 1280 10 930) (lget W k)) <
      2 ^ 59520 := fun k => by
    exact packD_lt (d := 10) (n := 930) (by norm_num)
      (fun i hi => testBit_keyB_high (d := 10) (by norm_num) _ i hi)
  have hl : lane64 (stackN 59520 28 fun y2 =>
      packD 10 (keyB (repN (2 ^ 248 - 1) 1280 10 930) (repN m63 1280 10 930) (lget W y2))) y =
      lane64 (packD 10 (keyB (repN (2 ^ 248 - 1) 1280 10 930) (repN m63 1280 10 930)
        (lget W (y / 930)))) (y % 930) := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [testBit_lane64, testBit_lane64, testBit_stackN_s (by omega) hF]
    by_cases hi : i < 64
    · have e1 : (64 * y + i) / 59520 = y / 930 := by omega
      have e2 : (64 * y + i) % 59520 = 64 * (y % 930) + i := by omega
      have h3 : y / 930 < 28 := by omega
      simp [hi, e1, e2, h3]
    · simp [hi]
  rw [hl, lane64_packD (by omega : y % 930 < 2 ^ 10), lane_keyB (by norm_num) (by omega)]
  exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (keyL_lt _) (by norm_num))

end CFSG.Certificates.ThDemp.Batches

end
