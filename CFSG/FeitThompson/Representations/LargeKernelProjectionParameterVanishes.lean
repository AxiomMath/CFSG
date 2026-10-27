module

public import Mathlib.Basic.Real.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

theorem eq_zero_of_sq_mul_sub_one_div_sub_two_mul_le
    {p e h a : ℤ} (hp : 3 ≤ p) (he : 1 ≤ e) (hh : p ^ 2 ≤ h) (hep : 2 * e ≤ p + 1)
    (ha : (a : ℝ) ^ 2 * ((h : ℝ) - 1) / (e : ℝ) - 2 * (a : ℝ) ≤ (e : ℝ) - 1) :
    a = 0 := by
  have hE : (0 : ℝ) < (e : ℝ) := by exact_mod_cast lt_of_lt_of_le zero_lt_one he
  have h3 : a ^ 2 * (h - 1) - 2 * a * e ≤ (e - 1) * e := by
    have h1 := mul_le_mul_of_nonneg_right ha hE.le
    rw [sub_mul, div_mul_cancel₀ _ (ne_of_gt hE)] at h1
    have : ((a ^ 2 * (h - 1) - 2 * a * e : ℤ) : ℝ) ≤ (((e - 1) * e : ℤ) : ℝ) := by
      push_cast; linarith
    exact_mod_cast this
  by_contra hne
  set A : ℤ := |a| with hAdef
  have hA1 : 1 ≤ A := Int.one_le_abs hne
  have hsq : a ^ 2 = A ^ 2 := (sq_abs a).symm
  have hle : a ≤ A := le_abs_self a
  have he0 : (0 : ℤ) < e := lt_of_lt_of_le zero_lt_one he
  have hstep : A ^ 2 * (h - 1) - 2 * A * e ≤ (e - 1) * e := by
    have : 2 * a * e ≤ 2 * A * e := mul_le_mul_of_nonneg_right (by linarith) he0.le
    rw [hsq] at h3; linarith
  have hh1 : (p - 1) * (2 * e) ≤ h - 1 := by nlinarith
  have hmul : A ^ 2 * ((p - 1) * (2 * e)) ≤ A ^ 2 * (h - 1) :=
    mul_le_mul_of_nonneg_left hh1 (sq_nonneg A)
  have hc : A ^ 2 * ((p - 1) * (2 * e)) - 2 * A * e ≤ (e - 1) * e := by linarith
  have t1 : 0 ≤ e * (p - 1) * (A ^ 2 - A) := by
    have : A ≤ A ^ 2 := by nlinarith
    exact mul_nonneg (mul_nonneg he0.le (by linarith)) (by linarith)
  have t2 : 0 ≤ e * (p - 2) * (A - 1) :=
    mul_nonneg (mul_nonneg he0.le (by linarith)) (by linarith)
  have t3 : e * (2 * (e - 1)) ≤ e * (p - 1) := mul_le_mul_of_nonneg_left (by linarith) he0.le
  have t4 : 1 * 2 ≤ e * (3 * p - 7) := mul_le_mul he (by linarith) (by norm_num) he0.le
  nlinarith [t1, t2, t3, t4, hc]

end CFSG.FeitThompson
