module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.LyonsUnitaryFour

theorem inv_pos_le_of_le {x A : ℤ} (hA : 0 < A) (h : A ≤ x) :
    0 < (x : ℚ)⁻¹ ∧ (x : ℚ)⁻¹ ≤ 1 / (A : ℚ) := by
  have hA' : (0 : ℚ) < A := by exact_mod_cast hA
  have hx : (A : ℚ) ≤ x := by exact_mod_cast h
  refine ⟨inv_pos.mpr (lt_of_lt_of_le hA' hx), ?_⟩
  rw [one_div]
  exact inv_anti₀ hA' hx

theorem inv_neg_ge_of_le {x B : ℤ} (hB : 0 < B) (h : x ≤ -B) :
    -(1 / (B : ℚ)) ≤ (x : ℚ)⁻¹ ∧ (x : ℚ)⁻¹ < 0 := by
  have hB' : (0 : ℚ) < B := by exact_mod_cast hB
  have hx : (x : ℚ) ≤ -B := by exact_mod_cast h
  have hxneg : (x : ℚ) < 0 := by linarith
  refine ⟨?_, inv_lt_zero.mpr hxneg⟩
  have h1 : (B : ℚ) ≤ -(x : ℚ) := by linarith
  have h2 : (-(x : ℚ))⁻¹ ≤ (B : ℚ)⁻¹ := inv_anti₀ hB' h1
  rw [inv_neg] at h2
  rw [one_div]
  linarith

theorem inv_mem_of_le_or_le {x A B : ℤ} (hA : 0 < A) (hB : 0 < B) (h : A ≤ x ∨ x ≤ -B) :
    -(1 / (B : ℚ)) ≤ (x : ℚ)⁻¹ ∧ (x : ℚ)⁻¹ ≤ 1 / (A : ℚ) := by
  rcases h with h | h
  · obtain ⟨h1, h2⟩ := inv_pos_le_of_le hA h
    have : (0 : ℚ) < 1 / B := by
      have : (0 : ℚ) < B := by exact_mod_cast hB
      positivity
    exact ⟨by linarith, h2⟩
  · obtain ⟨h1, h2⟩ := inv_neg_ge_of_le hB h
    have : (0 : ℚ) < 1 / A := by
      have : (0 : ℚ) < A := by exact_mod_cast hA
      positivity
    exact ⟨h1, by linarith⟩

theorem pos_lt_of_lt_inv {x : ℤ} {c : ℚ} (hc : 0 < c) (h : c < (x : ℚ)⁻¹) :
    0 < x ∧ (x : ℚ) < 1 / c := by
  have hpos : (0 : ℚ) < (x : ℚ)⁻¹ := lt_trans hc h
  have hx : (0 : ℚ) < x := inv_pos.mp hpos
  refine ⟨by exact_mod_cast hx, ?_⟩
  rw [one_div]
  calc (x : ℚ) = ((x : ℚ)⁻¹)⁻¹ := (inv_inv _).symm
    _ < c⁻¹ := inv_strictAnti₀ hc h

theorem neg_gt_of_inv_lt {x : ℤ} {c : ℚ} (hc : c < 0) (h : (x : ℚ)⁻¹ < c) :
    x < 0 ∧ 1 / c < (x : ℚ) := by
  have hneg : (x : ℚ)⁻¹ < 0 := lt_trans h hc
  have hx : (x : ℚ) < 0 := inv_lt_zero.mp hneg
  refine ⟨by exact_mod_cast hx, ?_⟩
  have h1 : -c < -(x : ℚ)⁻¹ := by linarith
  have h2 := pos_lt_of_lt_inv (x := -x) (c := -c) (by linarith)
    (by push_cast; rw [inv_neg]; exact h1)
  push_cast at h2
  rw [one_div] at h2 ⊢
  rw [inv_neg] at h2
  linarith [h2.2]

end CFSG.LyonsUnitaryFour
