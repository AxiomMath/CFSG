module

public import Mathlib.Tactic.FieldSimp
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Tactic.Ring.RingNF

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

variable {e h : ℝ}

theorem frobenius_deficit_denom_pos (he : 1 < e) (hh : 2 * e + 1 ≤ h) :
    0 < e ∧ 0 < h ∧ 0 < h + 2 :=
  ⟨by linarith, by linarith, by linarith⟩

theorem frobenius_deficit_eq (he : 1 < e) (hh : 2 * e + 1 ≤ h) :
    1 - e / h - (h - 1) / (e * h) - (e - 1) / (h + 2)
      = (e - 1) * ((h - 2 * e - 1) / (e * h) + 2 / (h * (h + 2))) := by
  obtain ⟨h0, h1, h2⟩ := frobenius_deficit_denom_pos he hh
  field_simp
  ring

theorem frobenius_deficit_pos (he : 1 < e) (hh : 2 * e + 1 ≤ h) :
    0 < 1 - e / h - (h - 1) / (e * h) - (e - 1) / (h + 2) := by
  obtain ⟨h0, h1, h2⟩ := frobenius_deficit_denom_pos he hh
  rw [frobenius_deficit_eq he hh]
  have hA : 0 ≤ (h - 2 * e - 1) / (e * h) := div_nonneg (by linarith) (by positivity)
  have hB : 0 < 2 / (h * (h + 2)) := by positivity
  exact mul_pos (by linarith) (by linarith)

end CFSG.FeitThompson
