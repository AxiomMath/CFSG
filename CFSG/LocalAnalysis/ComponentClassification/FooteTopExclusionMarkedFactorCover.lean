module

public import CFSG.LocalAnalysis.ComponentClassification.FooteTopExclusionMarkedAbsorption
public import CFSG.LocalAnalysis.ComponentClassification.FooteTopExclusionMarkedNormalizer
import CFSG.LocalAnalysis.ComponentClassification.FooteMarkedAbsorptionTools
import CFSG.LocalAnalysis.ComponentClassification.FooteMarkedFactorCoverTools
import CFSG.LocalAnalysis.ComponentClassification.FooteMarkedSemisimpleTools
public import CFSG.LocalAnalysis.ComponentClassification.FooteMarkedCanonicalLift

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup

@[expose] def FooteMarkedRankThreeAbsorption : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L : Subgroup G) (𝓢 : Set (Subgroup G)),
    FooteSwapSetting G t L 𝓢 →
    ∀ H : Subgroup G, H ≠ ⊤ →
    ∀ (a : ↥H ⧸ pPrimeCore 2 ↥H) (A : Subgroup (↥H ⧸ pPrimeCore 2 ↥H)), orderOf a = 2 →
      A ≤ centralizer ({a} : Set (↥H ⧸ pPrimeCore 2 ↥H)) →
      IsComponent (A.subgroupOf (centralizer ({a} : Set (↥H ⧸ pPrimeCore 2 ↥H)))) →
      FooteMarked.Marked 𝓢 (L ⧸ Open.fusionZStar L) (FooteMarked.canonicalPerfectLift H A) →
      Nonempty (↥A ⧸ center ↥A ≃* L ⧸ Open.fusionZStar L) → Odd (Nat.card (center ↥A)) →
      3 ≤ CFSG.pRank 2 ↥(centralizer (A : Set (↥H ⧸ pPrimeCore 2 ↥H))) →
      IsComponent A

theorem footeMarkedFactorCover_of_rankThree (hRL : FooteMarkedRelativeLift)
    (h71 : FooteMarkedRankThreeAbsorption) : FooteMarkedFactorCover := by
  intro G _ _ t L 𝓢 hset N H hN hNH hH K hK
  haveI : IsSimpleGroup (L ⧸ Open.fusionZStar L) :=
    (GrSLit.fusionZStar_quotient_of_isPComponent hset.2.1.1.2.2.1.2.1
      hset.2.1.1.2.2.1.2.2).1
  have hFam := hset.2.2.2.2.1
  have hT4 := FooteMarked.exists_isKleinFour_of_footeFamilyType hset.2.1.1.2.2.2.2.1
  obtain ⟨E, hEN, hEK, hE, hE8⟩ := FooteMarked.exists_isElementaryAbelian_le_base hFam hT4 hN hK
  obtain ⟨a, haE, ha2⟩ :=
    FooteMarked.exists_orderOf_eq_two_of_isElementaryAbelian hE (le_trans (by norm_num) hE8)
  have hbase : twoLayerIn N ≤ FooteMarked.base N := by
    rw [FooteMarked.base]; exact le_sup_right
  have hKH : K ≤ H := ((le_twoLayerIn_of_isTwoComponentIn hK.1).trans hbase).trans hNH
  have haH : a ∈ H := hNH (hEN haE)
  have ha : orderOf (⟨a, haH⟩ : ↥H) = 2 := by rw [Subgroup.orderOf_mk]; exact ha2
  obtain ⟨hAa, hA, hP, hAT, hZ⟩ := hRL G t L 𝓢 hset H K hH hK.2 hKH ⟨a, haH⟩ ha (hEK haE)
  have h3 := FooteMarked.three_le_pRank_centralizer_map_fixedShadowAt hKH (hEN.trans hNH) hEK hE
    hE8 (a := ⟨a, haH⟩) haE (LocalCores.isQuasisimple_of_mulEquiv (subgroupOfEquivOfLe hAa) hA.1)
  have hAc : IsComponent (relativeShadow H K a) := h71 G t L 𝓢 hset H hH _ _
    (FooteMarked.orderOf_mk_eq_two ha) hAa hA hP hAT hZ h3
  have hKA := FooteMarked.map_eq_map_fixedShadowAt hFam hK.2 hKH ha (hEK haE) hAc
  have hKJ : K ≤ FooteMarked.ambientCanonicalLift H (relativeShadow H K a) :=
    le_ambientCanonicalLift_of_isPerfect hK.2.1 hKH hKA.le
  have hJ : FooteMarked.canonicalPerfectLift H (relativeShadow H K a) =
      FooteMarked.ambientCanonicalLift H (relativeShadow H K a) :=
    FooteMarked.canonicalPerfectLift_eq_ambientCanonicalLift hAc
  refine ⟨FooteMarked.canonicalPerfectLift H (relativeShadow H K a), ⟨?_, hP⟩, ?_⟩
  · rw [hJ]
    exact FooteMarked.ambientCanonicalLift_isTwoComponentIn hAc
  · rw [hJ]
    exact FooteMarked.sup_oddCoreIn_ambientCanonicalLift hAc hKH hKA hKJ

end CFSG.ComponentClassification.FooteLit
