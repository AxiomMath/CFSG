module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionClassFourGroupHull

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionDoubleTransitiveNormalizer

open CFSG.Open CFSG.ShultStronglyClosedTI
open CFSG.BenderSuzuki.PFAppendixIII (rightConjugateElem)
open CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry

variable {G : Type*} [Group G]

theorem internal_involution_hull_image_eq_class_closure
    (N : Subgroup G) (z : G) (hzN : z ∈ N) :
    (involutionPointHull (⟨z, hzN⟩ : N)).map N.subtype =
      Subgroup.closure (conjugacyWithin N z) := by
  rw [involutionPointHull, MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨a, ⟨n, rfl⟩, rfl⟩
    exact ⟨n, rfl⟩
  · rintro ⟨n, rfl⟩
    exact ⟨rightConjugateElem (⟨z, hzN⟩ : N) n, ⟨n, rfl⟩, rfl⟩

theorem internal_involution_hull_rank_two_of_noncentral_odd_quotient
    [Finite G] (z : G) (hz : orderOf z = 2)
    (hnoncentral : QuotientGroup.mk' (CFSG.oddCore G) z ∉
      Subgroup.center (G ⧸ CFSG.oddCore G)) :
    2 ≤ CFSG.Open.twoRank (involutionPointHull z) := by
  by_contra hrank
  have hsmall : CFSG.Open.twoRank (involutionPointHull z) ≤ 1 := by omega
  exact hnoncentral (native_zStar_of_isolated_involution hz
    (involution_hull_rank_le_one_isolated hz hsmall)).1

theorem internal_involution_hull_rank_eq_original_class_closure
    [Finite G] (N : Subgroup G) (z : G) (hzN : z ∈ N) :
    CFSG.Open.pRank 2 (Subgroup.closure (conjugacyWithin N z)) =
      CFSG.Open.twoRank (involutionPointHull (⟨z, hzN⟩ : N)) := by
  rw [CFSG.Open.twoRank, ← pRank_subgroup_eq_internal_top 2 (by decide)]
  let L := involutionPointHull (⟨z, hzN⟩ : N)
  have hrank := pRank_top_eq_of_equiv 2 (by decide)
    (L.equivMapOfInjective N.subtype N.subtype_injective)
  rw [← pRank_subgroup_eq_internal_top 2 (by decide) L,
    ← pRank_subgroup_eq_internal_top 2 (by decide) (L.map N.subtype)] at hrank
  change CFSG.Open.pRank 2 (Subgroup.closure (conjugacyWithin N z)) = CFSG.Open.pRank 2 L
  rw [← internal_involution_hull_image_eq_class_closure N z hzN]
  exact hrank.symm

theorem original_subgroup_class_hull_rank_two_of_noncentral_odd_quotient
    [Finite G] (N : Subgroup G) (z : G) (hzN : z ∈ N) (hz : orderOf z = 2)
    (hnoncentral : QuotientGroup.mk' (CFSG.oddCore N) (⟨z, hzN⟩ : N) ∉
      Subgroup.center (N ⧸ CFSG.oddCore N)) :
    2 ≤ CFSG.Open.pRank 2 (Subgroup.closure (conjugacyWithin N z)) := by
  rw [internal_involution_hull_rank_eq_original_class_closure N z hzN]
  exact internal_involution_hull_rank_two_of_noncentral_odd_quotient
    (⟨z, hzN⟩ : N) ((Subgroup.orderOf_coe _).symm.trans hz) hnoncentral

end CFSG.ProperTwoGeneratedCore.LocalCriterionDoubleTransitiveNormalizer
