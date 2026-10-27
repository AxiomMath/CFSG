module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointSylowGeometry

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry

open CFSG.Open CFSG.ShultStronglyClosedTI CFSG.BenderSuzuki
open CFSG.BenderSuzuki.PFAppendixIII
open CFSG.ProperTwoGeneratedCore.LocalCriterionSubgroupSylow

variable {G : Type*} [Group G]

theorem pair_flip_zpowers_subgroupOf (H : Subgroup G)
    (beta : rightCosetSpace H) (t : G) :
    (Subgroup.zpowers t).subgroupOf (pairFlipGroup H beta t) =
      Subgroup.zpowers (⟨t, flip_mem_pairFlipGroup H beta t⟩ : pairFlipGroup H beta t) := by
  apply Subgroup.map_injective (pairFlipGroup H beta t).subtype_injective
  rw [Subgroup.map_subgroupOf_eq_of_le
    (show Subgroup.zpowers t ≤ pairFlipGroup H beta t from le_sup_right),
    MonoidHom.map_zpowers]
  rfl

theorem pair_group_stabilizer_sup_flip_eq_top (H : Subgroup G)
    (beta : rightCosetSpace H) (t : G) :
    (pairPointStabilizer H beta).subgroupOf (pairFlipGroup H beta t) ⊔
      Subgroup.zpowers (⟨t, flip_mem_pairFlipGroup H beta t⟩ : pairFlipGroup H beta t) = ⊤ := by
  rw [← pair_flip_zpowers_subgroupOf,
    ← Subgroup.subgroupOf_sup
      (pairPointStabilizer_le_pairFlipGroup H beta t)
      (show Subgroup.zpowers t ≤ pairFlipGroup H beta t from le_sup_right)]
  exact Subgroup.subgroupOf_self _

theorem pair_odd_core_restriction_le_stabilizer [Finite G]
    (H : Subgroup G) (beta : rightCosetSpace H) (t : G) :
    (pairOddCore H beta).subgroupOf (pairFlipGroup H beta t) ≤
      (pairPointStabilizer H beta).subgroupOf (pairFlipGroup H beta t) :=
  Subgroup.subgroupOf_mono _ (pairOddCore_le H beta t).1

theorem pair_odd_core_restriction_odd [Finite G]
    (H : Subgroup G) (beta : rightCosetSpace H) (t : G) :
    Odd (Nat.card ((pairOddCore H beta).subgroupOf (pairFlipGroup H beta t))) := by
  rw [Nat.card_congr
    (Subgroup.subgroupOfEquivOfLe (pairOddCore_le H beta t).2.1).toEquiv]
  exact pairOddCore_odd H beta

theorem pair_flip_restriction_order_two
    {H : Subgroup G} {z t : G} (hz : orderOf z = 2)
    {beta : rightCosetSpace H} (ht : t ∈ rightPairFlipFiber H z beta) :
    orderOf (⟨t, flip_mem_pairFlipGroup H beta t⟩ : pairFlipGroup H beta t) = 2 :=
  (Subgroup.orderOf_coe _).symm.trans (order_two_of_mem_pointClass hz ht.1)

theorem pair_restricted_t_centralizer_index_eq_class_card [Finite G]
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta) :
    (Subgroup.centralizer
      ({(⟨t, flip_mem_pairFlipGroup H beta t⟩ : pairFlipGroup H beta t)} :
        Set (pairFlipGroup H beta t))).relIndex
      ((pairPointStabilizer H beta).subgroupOf (pairFlipGroup H beta t)) =
        Nat.card (conjugacyWithin H z) := by
  change ((Subgroup.centralizer
    ({(⟨t, flip_mem_pairFlipGroup H beta t⟩ : pairFlipGroup H beta t)} :
      Set (pairFlipGroup H beta t))).subgroupOf
        ((pairPointStabilizer H beta).subgroupOf (pairFlipGroup H beta t))).index = _
  rw [pair_subgroup_t_centralizer_eq]
  change ((Subgroup.centralizer ({t} : Set G)).subgroupOf
    (pairFlipGroup H beta t)).relIndex
      ((pairPointStabilizer H beta).subgroupOf (pairFlipGroup H beta t)) = _
  rw [Subgroup.relIndex_subgroupOf (pairPointStabilizer_le_pairFlipGroup H beta t)]
  exact pair_stabilizer_t_centralizer_index_eq_class_card h S hzS hzcenter hbeta ht

end CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
