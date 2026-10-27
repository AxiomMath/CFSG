module

public import CFSG.LocalAnalysis.ComponentInitial.KProperSolvableOddQuotientLayer
public import CFSG.LocalAnalysis.ComponentInitial.ThreeFactorConfiguration
public import CFSG.LocalAnalysis.ComponentInitial.EscapingNotAlternating

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup CFSG.ComponentClassification

theorem kProper_ordinary_local_B_pump_up {C : CFSG.Assembly.GroupProp} (hS : SchreierFor C) :
    KProperOrdinaryLocalBPumpUp C := by
  intro H _ _ hK hloc t ht J hJ
  have hinj : Function.Injective (QuotientGroup.mk' (⊥ : Subgroup H)) :=
    (MonoidHom.ker_eq_bot_iff _).1 (QuotientGroup.ker_mk' _)
  have himage : CFSG.Assembly.IsComponentOf (J.map (QuotientGroup.mk' (⊥ : Subgroup H)))
      (centralizer ({QuotientGroup.mk' (⊥ : Subgroup H) t} : Set (H ⧸ (⊥ : Subgroup H)))) := by
    have h := (isComponentOf_map_iff hinj).2 hJ
    rwa [map_centralizer_singleton_of_injective hinj,
      MonoidHom.range_eq_top.2 (QuotientGroup.mk'_surjective _), top_inf_eq] at h
  have hJp : Group.IsPerfect J := ((AssemblyBPredicates.isQuasisimple_iff_native J).1 hJ.2.2).1
  have hJ2 : J ≤ CFSG.pLayer H 2 :=
    kProper_solvable_odd_quotient_ordinary_local_image_enters_two_layer hS hK ⊥
      (by rw [Subgroup.card_bot]; exact odd_one) ht hJ.1 hJp himage
  have hpl : CFSG.pLayer H 2 ≤ CFSG.layer H := sSup_le fun Q hQ =>
    le_sSup ((AssemblyBPredicates.isComponentOf_top_iff_native Q).1
      (hloc Q ((isTwoPComponent_iff_isPComponent Q).2 hQ)))
  have hJE : J ≤ CFSG.layer H := hJ2.trans hpl
  obtain ⟨L, hL, hcases⟩ := involution_layer_component_orbit_location ht hJ hJE
  refine ⟨hJE, L, hL, ?_⟩
  rcases hcases with h | ⟨h1, h2, h3, h4, -, -⟩
  · exact Or.inl h
  · exact Or.inr ⟨h1, h2, h3, h4⟩

end CFSG.LocalAnalysis.ComponentInitial
