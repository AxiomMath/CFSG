module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionPairRootNonnestingFixedSets
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionPairRootNonnestingOpposite
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorPairRankLocalIdentification

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionPairRootNonnesting

open CFSG
open CFSG.Open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator

universe u

variable {G : Type u} [Group G]

theorem original_root_class_normalized
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z) :
    H ≤ Subgroup.normalizer (conjugacyWithin H z) := by
  have hclass : numeratorPairRankPointClass H z 1 = conjugacyWithin H z := by
    rw [numeratorPairRankPointClass, original_point_class_intersection_eq_conjugacyWithin h]
    ext x
    simp only [Set.mem_inter_iff, SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff,
      mul_one, one_mul, and_true]
  have hnorm := numeratorPairRankPointClass_normalized H z 1
  rw [hclass] at hnorm
  intro a ha
  apply hnorm
  exact ⟨ha, Subgroup.mem_centralizer_singleton_iff.mpr (by simp)⟩

theorem original_pair_generated_four_group_root_centralizer_nonnesting
    [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hgen : Subgroup.zpowers z ⊔ Subgroup.zpowers t ⊔ pairOddCore H beta = ⊤)
    (W : Subgroup G) [IsElementaryAbelian 2 W] (hcardW : Nat.card W = 4)
    (u v : G) (hW : W = Subgroup.closure ({u, v} : Set G))
    (hWB : W ≤ pairPointStabilizer H beta)
    (hzW : z ∈ Subgroup.centralizer (W : Set G))
    (htW : t ∈ Subgroup.centralizer (W : Set G)) :
    ¬ rootFixedSet H z v ⊆ rootFixedSet H z u ∨
      ¬ rootFixedSet H z (u * v) ⊆ rootFixedSet H z u := by
  classical
  by_contra hnest
  push Not at hnest
  obtain ⟨huW, _hvW, hu, _hv, _huv⟩ := elementary_four_group_generators W hcardW u v hW
  have hfull := original_nested_root_sets_eq_entire_class h S hzS hzcenter hbeta ht
    W hcardW u v hW hWB hzW htW hnest.1 hnest.2
  let U := Subgroup.closure (rootFixedSet H z u)
  have hUroot : U = Subgroup.closure (conjugacyWithin H z) := by
    change Subgroup.closure (rootFixedSet H z u) = Subgroup.closure (conjugacyWithin H z)
    rw [hfull]
  have hHU : H ≤ Subgroup.normalizer (U : Set G) := by
    rw [hUroot]
    exact (original_root_class_normalized h).trans (Subgroup.normalizer_le_normalizer_closure _)
  have hIU : pairOddCore H beta ≤ Subgroup.normalizer (U : Set G) :=
    (pairOddCore_le H beta t).2.2.trans hHU
  have hzclass : z ∈ conjugacyWithin H z := by
    refine ⟨1, ?_⟩
    simp only [Subgroup.coe_one, inv_one, one_mul, mul_one]
  have hzU : z ∈ U := by
    rw [hUroot]
    exact Subgroup.subset_closure hzclass
  have hUcentral : U ≤ Subgroup.centralizer ({u} : Set G) :=
    (Subgroup.closure_le _).mpr (fun _ hx => hx.2)
  have htorder : orderOf t = 2 := order_two_of_mem_pointClass h.distinguished_order ht.1
  have htt : t * t = 1 := by
    simpa only [pow_two] using (orderOf_eq_prime_iff.mp htorder).1
  have htI : t ∈ Subgroup.normalizer (pairOddCore H beta : Set G) := by
    let : ((pairOddCore H beta).subgroupOf (pairFlipGroup H beta t)).Normal :=
      pairOddCore_normal_in_pair_group h.distinguished_order hbeta ht
    exact (Subgroup.le_normalizer_of_normal_subgroupOf (pairOddCore_le H beta t).2.1)
      (flip_mem_pairFlipGroup H beta t)
  have htu : Commute t u := (Subgroup.mem_centralizer_iff.mp htW u huW).symm
  exact simple_opposite_join_contradiction hnonab (pairOddCore H beta) U z t u hzU
    (orderOf_eq_prime_iff.mp h.distinguished_order).2 (orderOf_eq_prime_iff.mp hu).2
    htt hIU htI hgen hUcentral htu

theorem original_pair_generated_four_group_root_centralizer_nonnesting_literal
    [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hgen : Subgroup.zpowers z ⊔ Subgroup.zpowers t ⊔ pairOddCore H beta = ⊤)
    (W : Subgroup G) [IsElementaryAbelian 2 W] (hcardW : Nat.card W = 4)
    (u v : G) (hW : W = Subgroup.closure ({u, v} : Set G))
    (hWB : W ≤ pairPointStabilizer H beta)
    (hzW : z ∈ Subgroup.centralizer (W : Set G))
    (htW : t ∈ Subgroup.centralizer (W : Set G)) :
    ¬ conjugacyWithin H z ∩ (Subgroup.centralizer ({v} : Set G) : Set G) ⊆
        conjugacyWithin H z ∩ (Subgroup.centralizer ({u} : Set G) : Set G) ∨
      ¬ conjugacyWithin H z ∩ (Subgroup.centralizer ({u * v} : Set G) : Set G) ⊆
        conjugacyWithin H z ∩ (Subgroup.centralizer ({u} : Set G) : Set G) :=
  original_pair_generated_four_group_root_centralizer_nonnesting hnonab h S hzS hzcenter
    hbeta ht hgen W hcardW u v hW hWB hzW htW

end CFSG.ProperTwoGeneratedCore.LocalCriterionPairRootNonnesting
