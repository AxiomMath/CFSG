module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.SporadicTableBasic
public import CFSG.LocalAnalysis.ComponentClassification.SuzOutComp
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCF23ONOutMain
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCF23ONOutK3Main
public import CFSG.Sporadic.ONOddCore.LocalComp
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.SporadicTableDefs

public section

namespace CFSG.ComponentClassification.CatFC

open CFSG Subgroup CFSG.Blueprint
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

section SuzRow


theorem sporadic_rows_suz {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (e : S ≃* NativeSporadic.Carrier .Suz)
    {σ : MulAut S} (hσ : orderOf σ = 2) {D : Subgroup (fixedSubgroup σ)}
    (hD : IsComponent D) :
    (σ ∈ (MulAut.conj : S →* MulAut S).range →
        SporadicInnerRow .Suz (Nat.card (D ⧸ center D))) ∧
      (σ ∉ (MulAut.conj : S →* MulAut S).range →
        SporadicOuterRow .Suz (Nat.card (D ⧸ center D))) := by
  refine ⟨fun hin => inner_row_of_centralizer hS hna hσ hD hin
      (P := fun c => c = 20160) (fun u hu B hB => ?_), fun hout => ?_⟩
  · exact Sporadic.SuzOddCore.CTI_Suz_involution_local_components_simple_quotient_order e u hu B hB
  · obtain ⟨B, hB, hcard⟩ := SeitzReduction.OmegaPilot.exists_component_fixSub σ hD
    rw [← hcard]
    exact ComponentClassification.SolMax.suzOuterComponentsInput_holds S ⟨e⟩ σ
      (mul_self_eq_one_of_orderOf_eq_two' hσ) hout B hB

end SuzRow

section ONanRow


theorem sporadic_rows_onan {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (e : S ≃* NativeSporadic.Carrier .ONan)
    {σ : MulAut S} (hσ : orderOf σ = 2) {D : Subgroup (fixedSubgroup σ)}
    (hD : IsComponent D) :
    (σ ∈ (MulAut.conj : S →* MulAut S).range →
        SporadicInnerRow .ONan (Nat.card (D ⧸ center D))) ∧
      (σ ∉ (MulAut.conj : S →* MulAut S).range →
        SporadicOuterRow .ONan (Nat.card (D ⧸ center D))) := by
  refine ⟨fun hin => inner_row_of_centralizer hS hna hσ hD hin
      (P := fun c => c = 20160) (fun u hu B hB => ?_), fun hout => ?_⟩
  · exact Sporadic.ONOddCore.cti_on_involution_local_components_projective_linear_quotient_order
      ⟨e⟩ u hu B hB
  · obtain ⟨B, hB, hcard⟩ := SeitzReduction.OmegaPilot.exists_component_fixSub σ hD
    rw [← hcard]
    exact ComponentClassification.SolMax.onOuterComponentsInput_of_local
      ComponentClassification.SolMax.ONOut.onOuterLocalInput_holds S ⟨e⟩ σ
      (mul_self_eq_one_of_orderOf_eq_two' hσ) hout B hB

end ONanRow

end CFSG.ComponentClassification.CatFC
