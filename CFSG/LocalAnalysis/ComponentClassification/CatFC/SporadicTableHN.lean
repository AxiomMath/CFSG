module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.SporadicTableBasic
public import CFSG.LocalAnalysis.SeitzReduction.SporadicRefineSym
public import CFSG.LocalAnalysis.ComponentClassification.SporRestrictedLocal
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.SporadicTableDefs

public section

namespace CFSG.ComponentClassification.CatFC

open CFSG Subgroup CFSG.Blueprint
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

section HNRow


theorem sporadic_rows_hn {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (e : S ≃* NativeSporadic.Carrier .HN)
    {σ : MulAut S} (hσ : orderOf σ = 2) {D : Subgroup (fixedSubgroup σ)}
    (hD : IsComponent D) :
    (σ ∈ (MulAut.conj : S →* MulAut S).range →
        SporadicInnerRow .HN (Nat.card (D ⧸ center D))) ∧
      (σ ∉ (MulAut.conj : S →* MulAut S).range →
        SporadicOuterRow .HN (Nat.card (D ⧸ center D))) := by
  refine ⟨fun hin => inner_row_of_centralizer hS hna hσ hD hin
      (P := fun c => c = 44352000) (fun u hu B hB => ?_), fun hout => ?_⟩
  · exact ComponentClassification.RestrictedStd.Spor.hnLocalComponentsInput_holds S e u hu B hB
  · exact SeitzReduction.SporadicRefine.hn_outer_card_quotient_center e hσ hout hD

end HNRow

end CFSG.ComponentClassification.CatFC
