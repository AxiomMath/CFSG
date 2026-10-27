module

public import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Tactic.FieldSimp
public import Mathlib.Basic.Real.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.Ring.RingNF

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

private lemma three_le_of_odd_prime {p : ℕ} (hp : p.Prime) (hodd : Odd p) : 3 ≤ p := by
  have h2 : 2 ≤ p := hp.two_le
  have hne : p ≠ 2 := by rintro rfl; revert hodd; decide
  omega

theorem oppositeKernel_numerical_contradiction {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpodd : Odd p) (hqodd : Odd q) (hqp : q < p) {u v k : ℝ} (hu0 : 0 < u) (hv0 : 0 < v)
    (hk0 : 0 < k) (hu : 2 * q < u) (hv : 2 * p < v) (hvpq : (p : ℝ) * q + 1 ≤ v)
    (hk : 2 * p * v < k) :
    (p : ℝ) * q / k + 2 / ((p : ℝ) * q) + 1 / (u * q) + 1 / (v * p) < 1 / (p : ℝ) + 1 / (q : ℝ) := by
  have hq3 : (3 : ℝ) ≤ (q : ℝ) := by
    have := three_le_of_odd_prime hq hqodd
    exact_mod_cast this
  have hp3 : (3 : ℝ) ≤ (p : ℝ) := by
    have := three_le_of_odd_prime hp hpodd
    exact_mod_cast this
  have hqp' : (q : ℝ) < (p : ℝ) := by exact_mod_cast hqp
  have hQ0 : (0 : ℝ) < (q : ℝ) := by linarith
  have hP0 : (0 : ℝ) < (p : ℝ) := by linarith
  have e1 : (p : ℝ) * q / k < 1 / (2 * (p : ℝ)) := by
    rw [div_lt_div_iff₀ hk0 (by positivity)]
    nlinarith [mul_pos hP0 hQ0]
  have e2 : 2 / ((p : ℝ) * q) < 2 / ((q : ℝ) * q) := by
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have e3 : 1 / (u * (q : ℝ)) < 1 / (2 * ((q : ℝ) * q)) := by
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have e4 : 1 / (v * (p : ℝ)) < 1 / (2 * ((q : ℝ) * q)) := by
    have hvp : 2 * (p : ℝ) * p < v * p := by nlinarith
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hsum : 2 / ((q : ℝ) * q) + 1 / (2 * ((q : ℝ) * q)) + 1 / (2 * ((q : ℝ) * q))
      = 3 / ((q : ℝ) * q) := by
    field_simp
    ring
  have e5 : 3 / ((q : ℝ) * q) ≤ 1 / (q : ℝ) := by
    rw [div_le_div_iff₀ (by positivity) hQ0]
    nlinarith
  have e6 : 1 / (2 * (p : ℝ)) < 1 / (p : ℝ) := by
    rw [div_lt_div_iff₀ (by positivity) hP0]
    linarith
  linarith

end CFSG.FeitThompson
