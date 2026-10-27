module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionMaximalPrimeFixedSets

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionDoubleTransitiveNormalizer

open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime

variable {G : Type*} [Group G]

@[expose] def restrictedRightCosetEmbedding (H N : Subgroup G) :
    pointRightCosetSpace (H.subgroupOf N) → pointRightCosetSpace H :=
  Quotient.map' (fun x : N => (x : G)) (fun x y hxy => by
    rw [QuotientGroup.rightRel_apply] at hxy ⊢
    exact hxy)

theorem restrictedRightCosetEmbedding_mk (H N : Subgroup G) (n : N) :
    restrictedRightCosetEmbedding H N (rightCosetMk (H.subgroupOf N) n) =
      rightCosetMk H (n : G) := rfl

theorem restrictedRightCosetEmbedding_injective (H N : Subgroup G) :
    Function.Injective (restrictedRightCosetEmbedding H N) := by
  intro a b
  refine Quotient.inductionOn₂ a b ?_
  intro x y hxy
  apply Quotient.sound
  change (QuotientGroup.rightRel (H.subgroupOf N)) x y
  rw [QuotientGroup.rightRel_apply]
  change Quotient.mk (QuotientGroup.rightRel H) (x : G) =
    Quotient.mk (QuotientGroup.rightRel H) (y : G) at hxy
  change (y : G) * (x : G)⁻¹ ∈ H
  exact QuotientGroup.rightRel_apply.mp (Quotient.exact hxy)

theorem restrictedRightCosetEmbedding_equivariant (H N : Subgroup G)
    (a : pointRightCosetSpace (H.subgroupOf N)) (n : N) :
    restrictedRightCosetEmbedding H N (pointRightCosetMul (H.subgroupOf N) a n) =
      pointRightCosetMul H (restrictedRightCosetEmbedding H N a) (n : G) := by
  refine Quotient.inductionOn a ?_
  intro x
  simp only [restrictedRightCosetEmbedding, Quotient.map'_mk,
    pointRightCosetMul_mk, Subgroup.coe_mul]

theorem restrictedRightCosetEmbedding_range (H N : Subgroup G) :
    Set.range (restrictedRightCosetEmbedding H N) =
      Set.range (fun n : N => pointRightCosetMul H (rightCosetMk H 1) (n : G)) := by
  ext a
  constructor
  · rintro ⟨b, rfl⟩
    refine Quotient.inductionOn b ?_
    intro n
    refine ⟨n, ?_⟩
    change pointRightCosetMul H (Quotient.mk (QuotientGroup.rightRel H) 1) (n : G) =
      Quotient.mk (QuotientGroup.rightRel H) (n : G)
    rw [pointRightCosetMul_mk, one_mul]
  · rintro ⟨n, rfl⟩
    refine ⟨rightCosetMk (H.subgroupOf N) n, ?_⟩
    change Quotient.mk (QuotientGroup.rightRel H) (n : G) =
      pointRightCosetMul H (Quotient.mk (QuotientGroup.rightRel H) 1) (n : G)
    rw [pointRightCosetMul_mk, one_mul]

theorem normalizer_restrictedRightCosetEmbedding_fixed
    (H A : Subgroup G) (hAH : A ≤ H)
    (a : pointRightCosetSpace (H.subgroupOf (Subgroup.normalizer (A : Set G)))) :
    restrictedRightCosetEmbedding H (Subgroup.normalizer (A : Set G)) a ∈
      pointFixedSet H A := by
  refine Quotient.inductionOn a ?_
  intro n g hg
  change pointRightCosetMul H (Quotient.mk (QuotientGroup.rightRel H) (n : G)) g =
    Quotient.mk (QuotientGroup.rightRel H) (n : G)
  have hh := normalizer_orbit_point_fixed hAH n.property hg
  simpa only [rightCosetMk, pointRightCosetMul_mk, one_mul] using hh

@[expose] def normalizerRightCosetFixedEmbedding (H A : Subgroup G) (hAH : A ≤ H) :
    pointRightCosetSpace (H.subgroupOf (Subgroup.normalizer (A : Set G))) →
      pointFixedSet H A :=
  fun a => ⟨restrictedRightCosetEmbedding H (Subgroup.normalizer (A : Set G)) a,
    normalizer_restrictedRightCosetEmbedding_fixed H A hAH a⟩

theorem normalizerRightCosetFixedEmbedding_injective
    (H A : Subgroup G) (hAH : A ≤ H) :
    Function.Injective (normalizerRightCosetFixedEmbedding H A hAH) := by
  intro a b hab
  exact restrictedRightCosetEmbedding_injective H (Subgroup.normalizer (A : Set G))
    (congrArg Subtype.val hab)

end CFSG.ProperTwoGeneratedCore.LocalCriterionDoubleTransitiveNormalizer
