module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDegreeIdentityInputs
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionPairSwap

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionDegreeIdentity

open CFSG.ShultStronglyClosedTI CFSG.BenderSuzuki.PFAppendixIII
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer

universe u

variable {G : Type u} [Group G] [Finite G]

theorem original_two_class_swap_fiber
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
    let F : Set G := {v | v ∈ involutionPointClass u ∧
      pointRightCosetMul H (rightCosetMk H 1) v = beta}
    F = conjugacyWithin D (u * t) ∧ u * t ∈ involutionPointClass u ∧
      Nat.card F = (Subgroup.centralizer ({u * t} : Set G)).relIndex D := by
  let D := pairPointStabilizer H beta
  let K := pairFlipGroup H beta t
  let J := oddCore K
  have hin := original_full_pair_swap_inputs h S hzS hzcenter beta hbeta
    u t hu huC ht hno htwo
  dsimp only at hin
  obtain ⟨hDnormal, hDindex, hfour, hJD, hJodd, hcentral,
    huK, htK, huDK, htDK, hutK, hdisj, hclasses, htfiber⟩ := hin
  let : (D.subgroupOf K).Normal := hDnormal
  have huI : IsInvolution u :=
    ⟨(orderOf_eq_prime_iff.mp hu).2, (orderOf_eq_prime_iff.mp hu).1⟩
  have htorder := order_two_of_mem_pointClass h.distinguished_order ht.1
  have htI : IsInvolution t :=
    ⟨(orderOf_eq_prime_iff.mp htorder).2, (orderOf_eq_prime_iff.mp htorder).1⟩
  have hclassesTop : ∀ v : G, IsInvolution v →
      v ∈ conjugacyWithin (⊤ : Subgroup G) u ∨
        v ∈ conjugacyWithin (⊤ : Subgroup G) t := by
    intro v hv
    simpa only [← point_class_eq_full_conjugacy] using hclasses v hv
  have hclassDistinct : conjugacyWithin (⊤ : Subgroup G) u ≠
      conjugacyWithin (⊤ : Subgroup G) t := by
    rw [← point_class_eq_full_conjugacy, ← point_class_eq_full_conjugacy]
    apply full_point_classes_ne u t
    intro hutclass
    exact Set.disjoint_left.mp hdisj (distinguished_mem_pointClass u) hutclass
  have htfiberTop : conjugacyWithin (⊤ : Subgroup G) t ∩
      ((K : Set G) \ (D : Set G)) = conjugacyWithin D t := by
    simpa only [← point_class_eq_full_conjugacy] using htfiber
  have hfull :=
    CFSG.ProperTwoGeneratedCore.LocalCriterionPairSwap.unique_rank_one_pair_stabilizer_two_swap_orbits_ambient
      K D (pairPointStabilizer_le_pairFlipGroup H beta t) J hDindex hJodd hJD hfour
      u t huI htI huC.1 (flip_mem_pairFlipGroup H beta t) htDK
      (Subgroup.mem_centralizer_singleton_iff.mp huC.2) hcentral
      hclassesTop hclassDistinct htfiberTop
  have hswap : {v | v ∈ involutionPointClass u ∧
      pointRightCosetMul H (rightCosetMk H 1) v = beta} =
        conjugacyWithin D (u * t) := by
    rw [← original_class_outside_eq_swap_fiber h.distinguished_order beta hbeta ht u hu]
    simpa only [← point_class_eq_full_conjugacy] using hfull.2.2.2.2.1
  refine ⟨hswap, ?_, ?_⟩
  · simpa only [← point_class_eq_full_conjugacy] using hfull.2.2.2.2.2
  · rw [hswap]
    exact hfull.2.2.2.1

end CFSG.ProperTwoGeneratedCore.LocalCriterionDegreeIdentity
