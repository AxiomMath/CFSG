module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDegreeIdentityCosets

public section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionDegreeIdentity

open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer

universe u

variable {G : Type u} [Group G]

theorem ambient_class_outside_image (D K : Subgroup G) (s : G) :
    Subtype.val '' {v : K | (v : G) ∈ involutionPointClass s ∧ v ∉ D.subgroupOf K} =
      involutionPointClass s ∩ ((K : Set G) \ (D : Set G)) := by
  ext v
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨hx.1, x.property, hx.2⟩
  · rintro ⟨hvclass, hvK, hvD⟩
    exact ⟨⟨v, hvK⟩, ⟨hvclass, hvD⟩, rfl⟩

theorem original_full_swap_fiber_subtype_image
    {H : Subgroup G} {z t : G} (hz : orderOf z = 2)
    (beta : rightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    (ht : t ∈ rightPairFlipFiber H z beta) (s : G) (hs : orderOf s = 2) :
    let D := pairPointStabilizer H beta
    let K := pairFlipGroup H beta t
    Subtype.val '' {v : K | (v : G) ∈ involutionPointClass s ∧ v ∉ D.subgroupOf K} =
      {v | v ∈ involutionPointClass s ∧
        pointRightCosetMul H (rightCosetMk H 1) v = beta} := by
  dsimp only
  rw [ambient_class_outside_image]
  exact original_class_outside_eq_swap_fiber hz beta hbeta ht s hs

end CFSG.ProperTwoGeneratedCore.LocalCriterionDegreeIdentity
