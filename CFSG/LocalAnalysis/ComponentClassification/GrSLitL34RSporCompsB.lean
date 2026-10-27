module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34RSporComps
public import CFSG.LocalAnalysis.ComponentClassification.SporRestrictedLocal
public import CFSG.Sporadic.FischerOddCore.FischerOuterFi22
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSporadicCasesD
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSporadicCases

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.Blueprint
open CFSG.ComponentClassification.RestrictedStd CFSG.ComponentClassification.RestrictedStd.Spor
open CFSG.ComponentClassification.OuterAutomorphisms

namespace L34R

theorem not_isL34Type_Co1
    {S : Type} [Group S] [Finite S] [IsSimpleGroup S] (hna : ∃ a b : S, a * b ≠ b * a)
    (e : S ≃* NativeSporadic.Carrier .Co1) {σ : MulAut S} {P : Subgroup S}
    (h : CatLeaf.ProperFixedComponent σ P) : ¬ IsL34Type (P ⧸ Open.fusionZStar P) := by
  refine not_isL34Type_of_comps CatalogueU.sporadicOddCoreFree_Co1
    (fun G _ _ ⟨e⟩ t ht B hB => ?_) (outer_of_forall_inner fun α => ?_) hna e h
  · refine not_small_of_card_quotient ?_
    rw [(co1LocalComponentsInput_holds G e t ht B hB).1]
    exact not_isSmallOrder_G24
  · obtain ⟨g, hg⟩ := Sporadic.Co1Schreier.full_automorphisms_inner_of_inputs
      Sporadic.Co2Schreier.CTUC_Co2_full_automorphisms_inner α
    exact ⟨g, hg.symm⟩

theorem not_isL34Type_Fi22
    {S : Type} [Group S] [Finite S] [IsSimpleGroup S] (hna : ∃ a b : S, a * b ≠ b * a)
    (e : S ≃* NativeSporadic.Carrier .Fi22) {σ : MulAut S} {P : Subgroup S}
    (h : CatLeaf.ProperFixedComponent σ P) : ¬ IsL34Type (P ⧸ Open.fusionZStar P) := by
  refine not_isL34Type_of_comps CatalogueU.sporadicOddCoreFree_Fi22
    (fun G _ _ ⟨e⟩ t ht B hB => ?_) (fun G _ _ _ _ hG α hα2 hα B hB => ?_) hna e h
  · refine not_small_of_card_quotient ?_
    rw [Sporadic.FischerOddCore.CTI_Fi22_involution_local_components_unitary_quotient_order e t ht
      B hB]
    exact not_isSmallOrder_U62
  · refine not_small_of_card_quotient ?_
    rcases Sporadic.FischerOddCore.fi22OuterComponentsInput_holds G hG α hα2 hα B hB with
      h | h <;> rw [h]
    · exact not_isSmallOrder_O8plus2
    · exact not_isSmallOrder_Sp62

end L34R

end CFSG.ComponentClassification.GrSLit
