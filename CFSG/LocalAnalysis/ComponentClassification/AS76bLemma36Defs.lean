module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingData
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ComponentClassification.AS76b

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding

section Star

variable {G : Type} [Group G]

@[expose] def Star36 (A R V : Subgroup G) : Prop :=
  ∀ x : G, rightConjugate R x ≤ V →
    ∃ y ∈ rightConjugate A x ⊓ normalizer (V : Set G), Odd (orderOf y) ∧
      (∀ b ∈ V ⊓ rightConjugate A x, ∀ c ∈ V ⊓ rightConjugate A x, b ≠ 1 → c ≠ 1 →
        ∃ k : ℕ, (y ^ k)⁻¹ * b * y ^ k = c) ∧
      ∀ z ∈ normalizer (rightConjugate A x : Set G) ⊓ normalizer (V : Set G),
        z⁻¹ * y * z ∈ zpowers y ⊔ centralizer (V : Set G)

end Star

end CFSG.ComponentClassification.AS76b
