module

public import Mathlib.Algebra.Group.End

public section

namespace CFSG.GroupTheory

open Equiv

variable {α : Type*} [DecidableEq α]

theorem conj_swap_mul_swap_eq_or_eq_inv {i j c : α} {σ : Perm α} (hij : i ≠ j) (hci : c ≠ i)
    (hcj : c ≠ j) (hσ : σ * swap i j = swap i j * σ) (hσc : σ c = c) :
    σ * (swap i j * swap j c) * σ⁻¹ = swap i j * swap j c ∨
      σ * (swap i j * swap j c) * σ⁻¹ = (swap i j * swap j c)⁻¹ := by
  have hjc : σ * swap j c * σ⁻¹ = swap (σ j) c := by
    rw [← swap_apply_apply, hσc]
  have hconj : σ * (swap i j * swap j c) * σ⁻¹ = swap i j * swap (σ j) c := by
    rw [← hjc, ← mul_assoc σ, hσ]
    simp only [mul_assoc]
  have hσi : σ i = swap i j (σ j) := by
    have h := congrArg (fun f : Perm α => f j) hσ
    simpa only [Perm.mul_apply, swap_apply_right] using h
  rw [hconj]
  by_cases hj : σ j = j
  · exact Or.inl (by rw [hj])
  · have hji : σ j = i := by
      by_cases h : σ j = i
      · exact h
      · exact absurd (σ.injective (hσi.trans (swap_apply_of_ne_of_ne h hj))) hij
    have hic : swap i j * swap i c * (swap i j)⁻¹ = swap j c := by
      rw [← swap_apply_apply, swap_apply_left, swap_apply_of_ne_of_ne hci hcj]
    refine Or.inr ?_
    rw [hji, mul_inv_rev, swap_inv, swap_inv, ← hic, inv_mul_cancel_right]

end CFSG.GroupTheory
