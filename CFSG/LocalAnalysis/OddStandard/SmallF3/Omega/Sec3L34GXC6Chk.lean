module

public import CFSG.GH74.KGroups.PermCheck
public import Std.Tactic.BVDecide.Normalize.BitVec

public section

namespace CFSG.OddStandard.SmallF3.Omega

open CFSG.Certificates CFSG.GH74.KGroups

variable {n : ℕ}

@[expose] def c6free (LA LP : List (Equiv.Perm (Fin n))) : Bool :=
  let LI := LA.filter fun τ => decide (τ ^ 2 = 1)
  (LP.filter fun y => decide (y ^ 2 = 1) && decide (y ≠ 1)).all fun y =>
    (LP.filter fun u => decide (u ^ 3 = 1) && decide (u ≠ 1) && decide (y * u = u * y)).all fun u =>
      LI.all fun τ =>
        bif decide (τ * y = y * τ) && decide (τ * u = u * τ) then decide (τ = 1) || decide (τ = y)
        else true

theorem c6free_sound (QA QP : RawSchreierDatum n) (hQA : ValidSchreier QA)
    (hQP : ValidSchreier QP) (h : c6free (elemsT QA) (elemsT QP) = true) :
    ∀ τ ∈ QA.originalSubgroup, τ ^ 2 = 1 → ∀ y ∈ QP.originalSubgroup, ∀ u ∈ QP.originalSubgroup,
      y ^ 2 = 1 → y ≠ 1 → u ^ 3 = 1 → u ≠ 1 → y * u = u * y → τ * y = y * τ → τ * u = u * τ →
      τ = 1 ∨ τ = y := by
  intro τ hτ hτ2 y hy u hu hy2 hy1 hu3 hu1 hyu hτy hτu
  have h1 := List.all_eq_true.1 h y (by
    rw [List.mem_filter]
    exact ⟨(mem_elemsT QP hQP y).2 hy, by simp [hy2, hy1]⟩)
  have h2 := List.all_eq_true.1 h1 u (by
    rw [List.mem_filter]
    exact ⟨(mem_elemsT QP hQP u).2 hu, by simp [hu3, hu1, hyu]⟩)
  have h3 := List.all_eq_true.1 h2 τ (by
    rw [List.mem_filter]
    exact ⟨(mem_elemsT QA hQA τ).2 hτ, by simp [hτ2]⟩)
  simpa [hτy, hτu] using h3

end CFSG.OddStandard.SmallF3.Omega
