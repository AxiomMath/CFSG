module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.SporadicTableBasic
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofMonster
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.SporadicTableDefs

public section

namespace CFSG.ComponentClassification.CatFC

open CFSG Subgroup CFSG.Blueprint
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

section MRow


theorem sporadic_rows_m {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (e : S ≃* NativeSporadic.Carrier .M) {σ : MulAut S}
    (hσ : orderOf σ = 2) {D : Subgroup (fixedSubgroup σ)} (hD : IsComponent D) :
    (σ ∈ (MulAut.conj : S →* MulAut S).range →
        SporadicInnerRow .M (Nat.card (D ⧸ center D))) ∧
      (σ ∉ (MulAut.conj : S →* MulAut S).range →
        SporadicOuterRow .M (Nat.card (D ⧸ center D))) := by
  refine ⟨fun _ => SeitzReduction.OmegaPilot.monster_two_part_card_quotient_center
      ComponentClassification.CatLeafProof.monsterInnerInput
      ComponentClassification.CatLeafProof.monsterLocalComponentsInput hS hna e hσ hD,
    fun hout => (hout (ComponentClassification.CatLeafProof.monsterInnerInput S hS ⟨e⟩ σ)).elim⟩

end MRow

section BRow


theorem sporadic_rows_b {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (e : S ≃* NativeSporadic.Carrier .B) {σ : MulAut S}
    (hσ : orderOf σ = 2) {D : Subgroup (fixedSubgroup σ)} (hD : IsComponent D) :
    (σ ∈ (MulAut.conj : S →* MulAut S).range →
        SporadicInnerRow .B (Nat.card (D ⧸ center D))) ∧
      (σ ∉ (MulAut.conj : S →* MulAut S).range →
        SporadicOuterRow .B (Nat.card (D ⧸ center D))) := by
  refine ⟨fun _ => SeitzReduction.OmegaPilot.baby_card_quotient_center hS hna e hσ hD,
    fun hout => (false_of_not_mem_range (ComponentClassification.BMCase.inner_of_equiv e
      RankThree.PartOne.SPOR.allInner_B σ) hout).elim⟩

end BRow

end CFSG.ComponentClassification.CatFC
