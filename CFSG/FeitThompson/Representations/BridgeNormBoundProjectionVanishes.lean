module

public import Mathlib.Data.Int.Notation
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Ring.RingNF

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

theorem eq_zero_of_sq_mul_sq_le_of_eq_mul_add {m n d a δ : ℤ} (hm : 3 ≤ m) (hn : 2 ≤ n)
    (hδ : δ = 1 ∨ δ = -1) (hd : d = n * m + δ) (hbound : d ^ 2 * a ^ 2 ≤ (n ^ 2 + 2) * m) :
    a = 0 := by
  by_contra ha
  have ha2 : 1 ≤ a ^ 2 := by
    rcases lt_trichotomy a 0 with h | h | h
    · nlinarith
    · exact absurd h ha
    · nlinarith
  have hnm : 6 ≤ n * m := by nlinarith
  have hdlow : n * m - 1 ≤ d := by rcases hδ with h | h <;> omega
  have hdpos : 0 < d := by omega
  have hsq : (n * m - 1) ^ 2 ≤ d ^ 2 := by nlinarith
  have hk : 2 ≤ n ^ 2 * (m - 1) - 2 * n - 2 := by
    nlinarith [mul_nonneg (sq_nonneg n) (sub_nonneg.2 hm),
      mul_nonneg (sub_nonneg.2 hn) (by linarith : (0 : ℤ) ≤ n + 1)]
  have key : (n ^ 2 + 2) * m < (n * m - 1) ^ 2 := by
    have hid : (n * m - 1) ^ 2 - (n ^ 2 + 2) * m = m * (n ^ 2 * (m - 1) - 2 * n - 2) + 1 := by
      ring
    nlinarith
  nlinarith

end CFSG.FeitThompson
