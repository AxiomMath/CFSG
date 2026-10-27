module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionMaximalPrimeFixedSets

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffine

open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime

variable {G : Type*} [Group G]

@[expose] def pointwiseRightStabilizer (H : Subgroup G)
    (Delta : Set (pointRightCosetSpace H)) : Subgroup G :=
  ⨅ omega : Delta, rightCosetStabilizer H omega.val

theorem mem_pointwiseRightStabilizer (H : Subgroup G)
    (Delta : Set (pointRightCosetSpace H)) (g : G) :
    g ∈ pointwiseRightStabilizer H Delta ↔
      ∀ omega ∈ Delta, pointRightCosetMul H omega g = omega := by
  simp only [pointwiseRightStabilizer, Subgroup.mem_iInf,
    mem_point_right_stabilizer_iff, Subtype.forall]

theorem subgroup_le_pointwiseRightStabilizer_fixed_set (H W : Subgroup G) :
    W ≤ pointwiseRightStabilizer H (pointFixedSet H W) := by
  intro w hw
  rw [mem_pointwiseRightStabilizer]
  exact fun omega homega => homega w hw

theorem pointwiseRightStabilizer_fixed_set_eq (H W : Subgroup G) :
    pointFixedSet H (pointwiseRightStabilizer H (pointFixedSet H W)) =
      pointFixedSet H W := by
  apply Set.Subset.antisymm
  · exact pointFixedSet_antitone (subgroup_le_pointwiseRightStabilizer_fixed_set H W)
  · intro omega homega k hk
    exact (mem_pointwiseRightStabilizer H _ k).mp hk omega homega

theorem pointwise_kernel_normalizer_preserves_fixed_set (H W : Subgroup G)
    (n : G)
    (hn : n ∈ Subgroup.normalizer
      (pointwiseRightStabilizer H (pointFixedSet H W) : Set G)) :
    ∀ omega ∈ pointFixedSet H W,
      pointRightCosetMul H omega n ∈ pointFixedSet H W := by
  rw [← pointwiseRightStabilizer_fixed_set_eq H W]
  exact fun _ homega => normalizer_preserves_pointFixedSet hn homega

theorem set_preserving_subgroup_le_pointwise_kernel_normalizer
    (H A : Subgroup G) (Delta : Set (pointRightCosetSpace H))
    (hstable : ∀ a ∈ A, ∀ omega ∈ Delta,
      pointRightCosetMul H omega a ∈ Delta) :
    A ≤ Subgroup.normalizer (pointwiseRightStabilizer H Delta : Set G) := by
  have hconj (a : G) (ha : a ∈ A) (k : G)
      (hk : k ∈ pointwiseRightStabilizer H Delta) :
      a * k * a⁻¹ ∈ pointwiseRightStabilizer H Delta := by
    rw [mem_pointwiseRightStabilizer] at hk ⊢
    intro omega homega
    rw [← pointRightCosetMul_mul, ← pointRightCosetMul_mul,
      hk _ (hstable a ha omega homega), pointRightCosetMul_mul,
      mul_inv_cancel, pointRightCosetMul_one]
  intro a ha
  apply Subgroup.mem_normalizer_iff.mpr
  intro k
  constructor
  · exact hconj a ha k
  · intro hk
    have hback := hconj a⁻¹ (A.inv_mem ha) (a * k * a⁻¹) hk
    simpa only [inv_inv, inv_mul_cancel_left, mul_assoc, inv_mul_cancel,
      mul_one] using hback

theorem prime_normalizer_le_pointwise_kernel_normalizer (H W : Subgroup G) :
    Subgroup.normalizer (W : Set G) ≤ Subgroup.normalizer
      (pointwiseRightStabilizer H (pointFixedSet H W) : Set G) := by
  exact set_preserving_subgroup_le_pointwise_kernel_normalizer H _ _
    (fun _ hn _ homega => normalizer_preserves_pointFixedSet hn homega)

theorem globally_maximal_prime_is_sylow_pointwise_kernel [Finite G]
    (H : Subgroup G) (p : ℕ) (W : Subgroup G) (hW : IsPGroup p W)
    (hthree : 3 ≤ Nat.card (pointFixedSet H W))
    (hmax : ∀ V : Subgroup G, IsPGroup p V → W ≤ V →
      3 ≤ Nat.card (pointFixedSet H V) → V ≤ W) :
    ∃ P : Sylow p (pointwiseRightStabilizer H (pointFixedSet H W)),
      (P : Subgroup (pointwiseRightStabilizer H (pointFixedSet H W))).map
        (pointwiseRightStabilizer H (pointFixedSet H W)).subtype = W := by
  let K := pointwiseRightStabilizer H (pointFixedSet H W)
  have hWK : W ≤ K := subgroup_le_pointwiseRightStabilizer_fixed_set H W
  let B := W.subgroupOf K
  have hB : IsPGroup p B := hW.comap_of_injective K.subtype K.subtype_injective
  obtain ⟨P, hBP⟩ := hB.exists_le_sylow
  let V := (P : Subgroup K).map K.subtype
  have hWV : W ≤ V := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hWK]
    exact Subgroup.map_mono hBP
  have hVK : V ≤ K := Subgroup.map_subtype_le (P : Subgroup K)
  have hfixed : pointFixedSet H W ⊆ pointFixedSet H V := by
    rw [← pointwiseRightStabilizer_fixed_set_eq H W]
    exact pointFixedSet_antitone hVK
  have hVthree : 3 ≤ Nat.card (pointFixedSet H V) := hthree.trans
    (Nat.card_le_card_of_injective (Set.inclusion hfixed) (Set.inclusion_injective hfixed))
  have hVW : V ≤ W := hmax V (P.isPGroup'.map K.subtype) hWV hVthree
  exact ⟨P, le_antisymm hVW hWV⟩

end CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffine
