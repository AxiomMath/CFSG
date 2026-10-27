module
public import Mathlib.Analysis.Real.Sqrt

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

theorem two_mul_mul_sqrt_lt_sub_one {e x : ℝ} (hx : 4 * e ^ 2 + 2 ≤ x) :
    2 * e * Real.sqrt x < x - 1 := by
  have hx0 : (0 : ℝ) ≤ x := by nlinarith [sq_nonneg e]
  have hs : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx0
  have hs0 : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  nlinarith [hs, hs0, sq_nonneg (Real.sqrt x - 2 * e), sq_nonneg (Real.sqrt x + 2 * e)]

theorem two_mul_mul_sqrt_lt_sub_one_of_lt {e n : ℕ} (hn : 4 * e ^ 2 + 1 < n) :
    2 * (e : ℝ) * Real.sqrt n < (n : ℝ) - 1 := by
  have h : 4 * e ^ 2 + 2 ≤ n := hn
  have h' : 4 * (e : ℝ) ^ 2 + 2 ≤ (n : ℝ) := by exact_mod_cast h
  exact two_mul_mul_sqrt_lt_sub_one h'

end CFSG.FeitThompson
