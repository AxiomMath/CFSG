module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.SporadicTableBasic
public import CFSG.LocalAnalysis.SeitzReduction.SporadicRefineL34He
public import CFSG.LocalAnalysis.SeitzReduction.SporadicRefineSUFi22
public import CFSG.Sporadic.Schreier.SteinbergBSLyOuterTrivial
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxPumpNotLie
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.SporadicTableDefs

public section

namespace CFSG.ComponentClassification.CatFC

open CFSG Subgroup CFSG.Blueprint
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

section HeRow


theorem sporadic_rows_he {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (e : S ≃* NativeSporadic.Carrier .He)
    {σ : MulAut S} (hσ : orderOf σ = 2) {D : Subgroup (fixedSubgroup σ)}
    (hD : IsComponent D) :
    (σ ∈ (MulAut.conj : S →* MulAut S).range →
        SporadicInnerRow .He (Nat.card (D ⧸ center D))) ∧
      (σ ∉ (MulAut.conj : S →* MulAut S).range →
        SporadicOuterRow .He (Nat.card (D ⧸ center D))) := by
  refine ⟨fun hin => inner_row_of_centralizer hS hna hσ hD hin
      (P := fun c => c = 20160) (fun u hu B hB => ?_), fun hout => ?_⟩
  · have h := Sporadic.SmallOddCore.cti_he_involution_local_components_simple_quotient_order
      ⟨e⟩ hu (isComponentOf_map_centralizer hB)
    rwa [card_quotient_center_map_centralizer] at h
  · have h1 := SeitzReduction.SporadicRefine.he_outer_card_fixedSubgroup e hσ hout
    have h2 := SeitzReduction.SporadicRefine.card_quotient_center_dvd_card_fixedSubgroup D
    rwa [h1] at h2

end HeRow

section LyRow


theorem sporadic_rows_ly {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (e : S ≃* NativeSporadic.Carrier .Ly)
    {σ : MulAut S} (hσ : orderOf σ = 2) {D : Subgroup (fixedSubgroup σ)}
    (hD : IsComponent D) :
    (σ ∈ (MulAut.conj : S →* MulAut S).range →
        SporadicInnerRow .Ly (Nat.card (D ⧸ center D))) ∧
      (σ ∉ (MulAut.conj : S →* MulAut S).range →
        SporadicOuterRow .Ly (Nat.card (D ⧸ center D))) := by
  refine ⟨fun hin => inner_row_of_centralizer hS hna hσ hD hin
      (P := fun c => c = 19958400) (fun u hu B hB => ?_), fun hout => ?_⟩
  · obtain ⟨hq, -, ⟨f⟩⟩ := Sporadic.LySchreier.involution_centralizers_quasisimple ⟨e⟩ u hu
    have hB' : B = ⊤ := SeitzReduction.UnitaryPilot.component_eq_top_of_central_kernel
      (QuotientGroup.mk' (center ↥(centralizer ({u} : Set S)))) (QuotientGroup.mk'_surjective _)
      (by rw [QuotientGroup.ker_mk']) hq.2.1 hq.1.commutator_eq_top hB
    subst hB'
    have h := ComponentClassification.SolMax.card_of_mulEquiv_alt (m := 11) (by norm_num) f
    rw [Nat.card_congr (QuotientGroup.congr _ _ Subgroup.topEquiv
      (Subgroup.map_center_eq _)).toEquiv, h]
    rfl
  · exact (false_of_not_mem_range (exists_conj_of_inner_eq_top e
      ComponentClassification.RestrictedStd.Spor.lyOuterTrivialInput σ) hout).elim

end LyRow

end CFSG.ComponentClassification.CatFC
