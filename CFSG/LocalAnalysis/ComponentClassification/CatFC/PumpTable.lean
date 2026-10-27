module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.PumpClause1
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.PumpClause3
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.PumpClause5
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.PumpBridge

public section

set_option linter.unusedSectionVars false

namespace CFSG.ComponentClassification.CatFC

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)


theorem kgPumpTableT_of_inputs (I : ArmInputs) (hT : EvenOuterTypedInput)
    (hHSO : HeSuzONNoAltEight)
    (hMcL : ∀ {S : Type} [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
      (S ≃* Carrier .McL) → ∀ {σ : MulAut S}, orderOf σ = 2 →
      σ ∈ (MulAut.conj : S →* MulAut S).range → ∀ {D : Subgroup ↥(fixedSubgroup σ)},
      IsComponent D → Nat.card (center ↥D) = 2) :
    EvenSporadicStandard.HSStd.Zassenhaus.Outer.KGPumpTableT := by
  intro S _ _ hcat hS τ hτ2 hτ1 N hNle hNq hNsub _
  have : IsSimpleGroup S := hS
  have hσ : orderOf τ = 2 := orderOf_eq_prime (by rw [sq]; exact hτ2) hτ1
  have hna : ∃ a b : S, a * b ≠ b * a := nonabelian_of_quasisimple hNq
  obtain ⟨D, hD, ⟨eDN⟩⟩ := fixedComponent_of_pump hNle hNq hNsub
  let eq : ↥D ⧸ center ↥D ≃* ↥N ⧸ center ↥N := quotientCenterEquiv eDN
  have hcZ : Nat.card (center ↥D) = Nat.card (center ↥N) := card_center_equiv eDN
  refine ⟨fun hA8 => ?_, fun j hj hA => ?_, fun hHS => ?_, fun hM => ?_, fun hH => ?_,
    fun i hi hL => ?_⟩
  · obtain ⟨e8⟩ := hA8
    rcases clause1_of_inputs I hT hHSO hMcL hna hcat hσ hD ⟨eq.trans e8⟩ with
      h | h | h | ⟨h1, h2⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr ⟨h1, hcZ ▸ h2⟩))
  · obtain ⟨eA⟩ := hA
    exact clause2_of_inputs I hna hcat hσ hD hj ⟨eq.trans eA⟩
  · obtain ⟨eH⟩ := hHS
    obtain ⟨h1, h2⟩ := clause3_of_inputs I hna hcat hσ hD ⟨eq.trans eH⟩
    exact ⟨h1, hcZ ▸ h2⟩
  · obtain ⟨eM⟩ := hM
    exact (clause4_of_inputs I hna hcat hσ hD).1 ⟨eq.trans eM⟩
  · obtain ⟨eH⟩ := hH
    exact (clause4_of_inputs I hna hcat hσ hD).2 ⟨eq.trans eH⟩
  · exact clause5_of_inputs I hT hna hcat hσ hD hi
      (CFSG.LieType.CurtisTits.lieModel_of_mulEquiv eq.symm hL)

end CFSG.ComponentClassification.CatFC
