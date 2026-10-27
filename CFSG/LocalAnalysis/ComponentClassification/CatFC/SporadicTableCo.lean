module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.SporadicTableBasic
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotCatSporadic
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatSporadicSix
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.SporadicTableDefs

public section

namespace CFSG.ComponentClassification.CatFC

open CFSG Subgroup CFSG.Blueprint
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

section Co1Row


theorem sporadic_rows_co1 {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (e : S ≃* NativeSporadic.Carrier .Co1) {σ : MulAut S}
    (hσ : orderOf σ = 2) {D : Subgroup (fixedSubgroup σ)} (hD : IsComponent D) :
    (σ ∈ (MulAut.conj : S →* MulAut S).range →
        SporadicInnerRow .Co1 (Nat.card (D ⧸ center D))) ∧
      (σ ∉ (MulAut.conj : S →* MulAut S).range →
        SporadicOuterRow .Co1 (Nat.card (D ⧸ center D))) := by
  refine ⟨fun _ => SeitzReduction.UnitaryPilot.co1_fixed_card_quotient hS hna e hσ hD,
    fun hout => (false_of_not_mem_range (ComponentClassification.BMCase.inner_of_equiv e
      RankThree.PartOne.SPOR.allInner_Co1 σ) hout).elim⟩

end Co1Row

section Co2Row


theorem sporadic_rows_co2 {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (e : S ≃* NativeSporadic.Carrier .Co2) {σ : MulAut S}
    (hσ : orderOf σ = 2) {D : Subgroup (fixedSubgroup σ)} (hD : IsComponent D) :
    (σ ∈ (MulAut.conj : S →* MulAut S).range →
        SporadicInnerRow .Co2 (Nat.card (D ⧸ center D))) ∧
      (σ ∉ (MulAut.conj : S →* MulAut S).range →
        SporadicOuterRow .Co2 (Nat.card (D ⧸ center D))) := by
  have h := SeitzReduction.UnitaryPilot.co2_false_of_fixed_component hS hna e hσ hD
  exact ⟨fun _ => h.elim, fun _ => h.elim⟩

end Co2Row

section Co3Row


theorem sporadic_rows_co3 {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (e : S ≃* NativeSporadic.Carrier .Co3) {σ : MulAut S}
    (hσ : orderOf σ = 2) {D : Subgroup (fixedSubgroup σ)} (hD : IsComponent D) :
    (σ ∈ (MulAut.conj : S →* MulAut S).range →
        SporadicInnerRow .Co3 (Nat.card (D ⧸ center D))) ∧
      (σ ∉ (MulAut.conj : S →* MulAut S).range →
        SporadicOuterRow .Co3 (Nat.card (D ⧸ center D))) := by
  refine ⟨fun _ => SeitzReduction.UnitaryPilot.co3_fixed_card_quotient hS hna e hσ hD,
    fun hout => (false_of_not_mem_range
      (RankThree.PartOne.CTUC_Co3_all_automorphisms_inner.2.2.2.2 S ⟨e⟩ σ) hout).elim⟩

end Co3Row

section J4Row


theorem sporadic_rows_j4 {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (e : S ≃* NativeSporadic.Carrier .J4) {σ : MulAut S}
    (hσ : orderOf σ = 2) {D : Subgroup (fixedSubgroup σ)} (hD : IsComponent D) :
    (σ ∈ (MulAut.conj : S →* MulAut S).range →
        SporadicInnerRow .J4 (Nat.card (D ⧸ center D))) ∧
      (σ ∉ (MulAut.conj : S →* MulAut S).range →
        SporadicOuterRow .J4 (Nat.card (D ⧸ center D))) := by
  have h := SeitzReduction.OmegaPilot.false_of_j4_component hS hna e hσ hD
  exact ⟨fun _ => h.elim, fun _ => h.elim⟩

end J4Row

section ThRow


theorem sporadic_rows_th {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (e : S ≃* NativeSporadic.Carrier .Th) {σ : MulAut S}
    (hσ : orderOf σ = 2) {D : Subgroup (fixedSubgroup σ)} (hD : IsComponent D) :
    (σ ∈ (MulAut.conj : S →* MulAut S).range →
        SporadicInnerRow .Th (Nat.card (D ⧸ center D))) ∧
      (σ ∉ (MulAut.conj : S →* MulAut S).range →
        SporadicOuterRow .Th (Nat.card (D ⧸ center D))) := by
  have h := SeitzReduction.LinearPilot.false_of_th_component hS hna e hσ hD
  exact ⟨fun _ => h.elim, fun _ => h.elim⟩

end ThRow

end CFSG.ComponentClassification.CatFC
