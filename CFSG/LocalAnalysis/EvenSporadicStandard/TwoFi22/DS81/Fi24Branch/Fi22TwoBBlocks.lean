module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.Fi22TwoBBlocksSpec
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.Fi22TwoBBlocksCent

public noncomputable section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.Fi22TwoB

open CFSG.ComponentClassification.CatFactsSmall.PSp43 (QA45)

theorem exists_quot_Cbar :
    ∃ (X : Type) (_ : Group X) (π : ↥Cbar →* X), Function.Surjective π ∧
      π.ker = Qbar.subgroupOf Cbar ∧ IsU42Two X := by
  obtain ⟨ρ, hrange, hker, -⟩ := exists_rho
  have hmem : ∀ g : ↥Cbar, ρ g ∈ QA45.originalSubgroup := fun g => hrange.le ⟨g, rfl⟩
  refine ⟨↥QA45.originalSubgroup, inferInstance, ρ.codRestrict QA45.originalSubgroup hmem, ?_, ?_,
    isU42Two_QA45⟩
  · intro x
    have hx : (x : Equiv.Perm (Fin 45)) ∈ ρ.range := hrange.ge x.2
    obtain ⟨g, hg⟩ := hx
    exact ⟨g, Subtype.ext hg⟩
  · rw [MonoidHom.ker_codRestrict, hker]

theorem cent_Qbar :
    Cbar ⊓ Subgroup.centralizer (Qbar : Set (Equiv.Perm (Fin 3510))) ≤ Qbar := by
  obtain ⟨X, _, π, hπ, hker, hX⟩ := exists_quot_Cbar
  exact cent_le_of_quot Cbar Qbar Qbar_le_Cbar π hπ hker hX exists_comm_not_mem_cent_mul

theorem O2In_Cbar :
    TwoFi22.O2In Cbar = Qbar := by
  obtain ⟨X, _, π, hπ, hker, hX⟩ := exists_quot_Cbar
  exact O2In_eq_of_quot Cbar Qbar Qbar_le_Cbar (IsPGroup.of_card card_Qbar) π hπ hker hX

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.Fi22TwoB
