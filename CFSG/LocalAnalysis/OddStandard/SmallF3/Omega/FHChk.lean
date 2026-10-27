module

public import CFSG.GH74.KGroups.PermCheck
public import Std.Tactic.BVDecide.Normalize.BitVec

public section

namespace CFSG.OddStandard.SmallF3.Omega

open CFSG.Certificates CFSG.GH74.KGroups

variable {n : ℕ}

@[expose] def fhO3Chk (LA LP : List (Equiv.Perm (Fin n))) : Bool :=
  let LU := LP.filter fun u => decide (u ^ 3 = 1) && decide (u ≠ 1)
  (LA.filter fun τ => decide (τ ^ 2 = 1)).all fun τ =>
    let LC := LP.filter fun c => decide (τ * c = c * τ)
    (LU.filter fun u => decide (τ * u = u * τ)).all fun u =>
      LC.any fun c => decide ((u * (c * u * c⁻¹)) ^ 27 ≠ 1)

theorem fhO3Chk_sound (QA QP : RawSchreierDatum n) (hQA : ValidSchreier QA)
    (hQP : ValidSchreier QP) (h : fhO3Chk (elemsT QA) (elemsT QP) = true) :
    ∀ τ ∈ QA.originalSubgroup, τ ^ 2 = 1 → ∀ u ∈ QP.originalSubgroup, u ^ 3 = 1 → u ≠ 1 →
      τ * u = u * τ →
      ∃ c ∈ QP.originalSubgroup, τ * c = c * τ ∧ (u * (c * u * c⁻¹)) ^ 27 ≠ 1 := by
  intro τ hτ hτ2 u hu hu3 hu1 hτu
  have h1 := List.all_eq_true.1 h τ (by
    rw [List.mem_filter]
    exact ⟨(mem_elemsT QA hQA τ).2 hτ, by simp [hτ2]⟩)
  have h2 := List.all_eq_true.1 h1 u (by
    rw [List.mem_filter]
    refine ⟨List.mem_filter.2 ⟨(mem_elemsT QP hQP u).2 hu, by simp [hu3, hu1]⟩, by simp [hτu]⟩)
  obtain ⟨c, hc, hc2⟩ := List.any_eq_true.1 h2
  rw [List.mem_filter] at hc
  exact ⟨c, (mem_elemsT QP hQP c).1 hc.1, by simpa using hc.2, by simpa using hc2⟩

end CFSG.OddStandard.SmallF3.Omega
