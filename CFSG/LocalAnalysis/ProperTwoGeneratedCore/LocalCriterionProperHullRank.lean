module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionProperHullDatum
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionClassFourGroupHull

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionProperHull

open CFSG.Open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionSubgroupSylow
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open CFSG.RankThreeCoreUniqueness.Helpers CFSG.TwoRankLowerBound.Helpers

universe u

variable {G : Type u} [Group G]

@[expose] def properOddCore (Y : Subgroup G) : Subgroup G :=
  (CFSG.oddCore Y).map Y.subtype

theorem properOddCore_le (Y : Subgroup G) : properOddCore Y ≤ Y :=
  Subgroup.map_subtype_le _

theorem subgroup_normalizes_properOddCore (Y : Subgroup G) :
    Y ≤ Subgroup.normalizer (properOddCore Y : Set G) := by
  simpa only [properOddCore, Subgroup.normalizer_eq_top, Subgroup.map_top,
    Subgroup.subtype_range] using
    (Subgroup.le_normalizer_map (H := CFSG.oddCore Y) Y.subtype)

theorem properOddCore_normal_in_subgroup (Y : Subgroup G) :
    ((properOddCore Y).subgroupOf Y).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (properOddCore_le Y)).mpr
    (subgroup_normalizes_properOddCore Y)

theorem properHull_subgroupOf (Y : Subgroup G) {z : G} (hzY : z ∈ Y) :
    (properHull Y z).subgroupOf Y = involutionPointHull (⟨z, hzY⟩ : Y) := by
  apply Subgroup.map_injective (f := Y.subtype) Y.subtype_injective
  rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (properHull_le Y hzY),
    internal_hull_map]

theorem properHull_normal_in_subgroup (Y : Subgroup G) {z : G} (hzY : z ∈ Y) :
    ((properHull Y z).subgroupOf Y).Normal := by
  rw [properHull_subgroupOf Y hzY]
  exact minimalLocalFailure_hull_normal _

variable [Finite G]

theorem properOddCore_card_odd (Y : Subgroup G) : Odd (Nat.card (properOddCore Y)) := by
  rw [properOddCore, Subgroup.card_map_of_injective Y.subtype_injective]
  exact CFSG.ComponentClassification.OddCore.odd_card Y

theorem properHull_rank_eq_internal (Y : Subgroup G) {z : G} (hzY : z ∈ Y) :
    twoRank (properHull Y z) = twoRank (involutionPointHull (⟨z, hzY⟩ : Y)) := by
  unfold twoRank
  exact (pRank_top_eq_of_equiv 2 (by decide) (properHullEquiv Y hzY)).symm

theorem properHull_rank_pos {H Y : Subgroup G} {z : G}
    (h : InvolutionPointLocalEmbedding H z) : 1 ≤ twoRank (properHull Y z) := by
  let zL : properHull Y z := ⟨z, distinguished_mem_properHull Y z⟩
  have hzorder : orderOf zL = 2 := (Subgroup.orderOf_coe zL).symm.trans h.distinguished_order
  apply le_twoRank_of_elementary (properHull Y z) (Subgroup.zpowers zL)
    (involution_zpowers_elementary zL hzorder) 1
  simpa only [pow_one] using (Nat.card_zpowers zL).trans hzorder

theorem properHull_not_le_point {H Y : Subgroup G} {z : G}
    (h : InvolutionPointLocalEmbedding H z) (hzY : z ∈ Y) (hescape : ¬ Y ≤ H) :
    ¬ properHull Y z ≤ H := by
  intro hle
  have hlocal := local_datum_subgroup_inheritance h Y hzY hescape
  apply minimalLocalFailure_hull_not_le_point hlocal
  intro x hx
  exact hle ((internal_hull_map Y hzY) ▸ Subgroup.mem_map_of_mem Y.subtype hx)

theorem properHull_central_sylow {H Y : Subgroup G} {z : G}
    (h : MinimalInvolutionPointLocalFailure H z) (hzY : z ∈ Y) (hescape : ¬ Y ≤ H) :
    InvolutionPointCentralSylow
      (⟨z, distinguished_mem_properHull Y z⟩ : properHull Y z) := by
  obtain ⟨_, hcentral⟩ := involution_point_subgroup_inheritance h.local_datum
    (properHull Y z) (distinguished_mem_properHull Y z)
    (properHull_not_le_point h.local_datum hzY hescape)
  exact hcentral h.central_sylow

theorem properHull_rank_one_isolated {H Y : Subgroup G} {z : G}
    (h : InvolutionPointLocalEmbedding H z) (hzY : z ∈ Y)
    (hrank : twoRank (properHull Y z) ≤ 1) :
    ∀ y : Y, Commute (y⁻¹ * (⟨z, hzY⟩ : Y) * y) (⟨z, hzY⟩ : Y) →
      y⁻¹ * (⟨z, hzY⟩ : Y) * y = (⟨z, hzY⟩ : Y) := by
  apply involution_hull_rank_le_one_isolated
  · exact (Subgroup.orderOf_coe (⟨z, hzY⟩ : Y)).symm.trans h.distinguished_order
  · rw [← properHull_rank_eq_internal Y hzY]
    exact hrank

end CFSG.ProperTwoGeneratedCore.LocalCriterionProperHull
