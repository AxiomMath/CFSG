module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDegreeIdentityPairData
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDegreeIdentityCosets
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDegreeIdentityNative

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionDegreeIdentity

open CFSG.ShultStronglyClosedTI CFSG.BenderSuzuki.PFAppendixIII
open CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer

universe u

variable {G : Type u} [Group G] [Finite G]

theorem original_full_pair_swap_inputs
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    (beta : rightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    (u t : G) (hu : orderOf u = 2)
    (huC : u ∈ pairPointStabilizer H beta ⊓ Subgroup.centralizer ({t} : Set G))
    (ht : t ∈ rightPairFlipFiber H z beta)
    (hno : ∀ E : Subgroup (pairPointStabilizer H beta),
      IsElementaryAbelian 2 E → Nat.card E ≠ 4)
    (htwo : ∀ v : G, orderOf v = 2 →
      v ∈ involutionPointClass u ∨ v ∈ involutionPointClass z) :
    let D := pairPointStabilizer H beta
    let K := pairFlipGroup H beta t
    let DK := D.subgroupOf K
    let J := oddCore K
    let uK : K := ⟨u, pairPointStabilizer_le_pairFlipGroup H beta t huC.1⟩
    let tK : K := ⟨t, flip_mem_pairFlipGroup H beta t⟩
    DK.Normal ∧ DK.index = 2 ∧ ¬ TwoRankAtLeastTwo DK ∧
      J ≤ DK ∧ Odd (Nat.card J) ∧
      QuotientGroup.mk' J tK ∈ Subgroup.center (K ⧸ J) ∧
      IsInvolution uK ∧ IsInvolution tK ∧ uK ∈ DK ∧ tK ∉ DK ∧ Commute uK tK ∧
      Disjoint (involutionPointClass u) (involutionPointClass t) ∧
      (∀ v : G, IsInvolution v →
        v ∈ involutionPointClass u ∨ v ∈ involutionPointClass t) ∧
      involutionPointClass t ∩ ((K : Set G) \ (D : Set G)) =
        conjugacyWithin D t := by
  have hnoD := no_two_rank_of_original_four_group_exclusion
    (pairPointStabilizer H beta) hno
  have hnoK := no_two_rank_subgroupOf
    (pairPointStabilizer H beta) (pairFlipGroup H beta t)
    (pairPointStabilizer_le_pairFlipGroup H beta t) hnoD
  have hcore := original_full_pair_odd_core_data h S hzS hzcenter beta hbeta t ht
  have hinvol := original_pair_group_involution_data h.distinguished_order beta hbeta
    u t hu huC.1 (Subgroup.mem_centralizer_singleton_iff.mp huC.2) ht
  have hclasses := original_two_distinct_flip_classes h beta hbeta u t huC.1 ht.1 htwo
  refine ⟨pair_stabilizer_normal h.distinguished_order hbeta ht,
    pair_group_index_two h.distinguished_order hbeta ht, hnoK,
    hcore.1, hcore.2.1, hcore.2.2,
    hinvol.1, hinvol.2.1, hinvol.2.2.1, hinvol.2.2.2.1, hinvol.2.2.2.2,
    hclasses.1, ?_, ?_⟩
  · intro v hv
    exact hclasses.2.2 v (orderOf_eq_prime hv.sq_eq_one hv.ne_one)
  · rw [hclasses.2.1]
    exact distinguished_class_outside_pair_group h S hzS hzcenter beta hbeta t ht

end CFSG.ProperTwoGeneratedCore.LocalCriterionDegreeIdentity
