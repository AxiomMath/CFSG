module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineKernel
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionClassFreeAffinePairs
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionMaximalPrimePairs

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffine

open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

variable {G : Type*} [Group G] [Finite G]

theorem class_involution_moves_point_of_three_set
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (Delta : Set (pointRightCosetSpace H)) (hthree : 3 ≤ Nat.card Delta)
    (s : G) (hs : s ∈ involutionPointClass z) :
    ∃ a ∈ Delta, a ≠ pointRightCosetMul H a s := by
  have huniq := ((involution_point_unique_containment_action
    h.distinguished_mem h.distinguished_order).2 h.unique_containment).2.1
  obtain ⟨epsilon, _, hu⟩ := huniq s hs
  have hcard : 1 < Delta.ncard := by
    change 1 < Nat.card Delta
    omega
  obtain ⟨a, ha, hne⟩ := Set.exists_ne_of_one_lt_ncard hcard epsilon
  exact ⟨a, ha, fun heq => hne (hu a heq.symm)⟩

theorem maximal_prime_pointwise_kernel_normalizer_class_free
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    (p : ℕ) (hp : p.Prime) (W : Subgroup G)
    (hW : IsPGroup p W) (hthree : 3 ≤ Nat.card (pointFixedSet H W))
    (hmax : ∀ V : Subgroup G, IsPGroup p V → W ≤ V →
      3 ≤ Nat.card (pointFixedSet H V) → V ≤ W)
    (hclassfree : involutionPointClass z ∩
      (Subgroup.normalizer (W : Set G) : Set G) = ∅) :
    involutionPointClass z ∩ (Subgroup.normalizer
      (pointwiseRightStabilizer H (pointFixedSet H W) : Set G) : Set G) = ∅ := by
  let : Fact p.Prime := ⟨hp⟩
  let K := pointwiseRightStabilizer H (pointFixedSet H W)
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro s ⟨hs, hsN⟩
  obtain ⟨a, ha, hab⟩ := class_involution_moves_point_of_three_set
    h (pointFixedSet H W) hthree s hs
  have hb : pointRightCosetMul H a s ∈ pointFixedSet H W :=
    pointwise_kernel_normalizer_preserves_fixed_set H W s hsN a ha
  have hKD : K ≤ rightCosetStabilizer H a ⊓
      rightCosetStabilizer H (pointRightCosetMul H a s) := by
    refine le_inf ?_ ?_
    · intro k hk
      exact (mem_point_right_stabilizer_iff H a k).mpr
        ((mem_pointwiseRightStabilizer H _ k).mp hk a ha)
    · intro k hk
      exact (mem_point_right_stabilizer_iff H _ k).mpr
        ((mem_pointwiseRightStabilizer H _ k).mp hk _ hb)
  obtain ⟨P, hsP⟩ := pair_normalized_subgroup_invariant_sylow h S hzS hzcenter
    a (pointRightCosetMul H a s) hab s hs rfl K hKD hsN p hp
  obtain ⟨R, hR⟩ := globally_maximal_prime_is_sylow_pointwise_kernel H p W hW hthree hmax
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq K P R
  have hmap : ((P : Subgroup K).map K.subtype).map
      (MulAut.conj (k : G)).toMonoidHom = W := by
    rw [← sylow_ambient_image_smul, hk]
    exact hR
  have hnorm := normalizer_map_automorphism_mem _ s hsP (MulAut.conj (k : G))
  rw [hmap] at hnorm
  let r := rightConjugateElem s (k : G)⁻¹
  have hrnorm : r ∈ Subgroup.normalizer (W : Set G) := by
    simpa only [r, rightConjugateElem, MulAut.conj_apply, inv_inv] using hnorm
  have hrclass : r ∈ involutionPointClass z := by
    rw [← pointClass_eq_of_mem hs]
    exact ⟨(k : G)⁻¹, rfl⟩
  have hempty : r ∈ (∅ : Set G) := hclassfree ▸ ⟨hrclass, hrnorm⟩
  exact hempty

end CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffine
