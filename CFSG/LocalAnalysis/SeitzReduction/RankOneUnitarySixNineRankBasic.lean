module

public import CFSG.GroupTheory.ABGLocalTools.Basic

public section

namespace CFSG.SeitzReduction.RankOne

namespace SixNineRank

open Subgroup CFSG.ABGLocalTools

@[expose] def RankCountInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (N U R X K : Subgroup G) (t v y ε : G),
    R ≤ X → X ≤ U → U ≤ K → K ≤ N →
    N ≤ normalizer (U : Set G) → N ≤ normalizer (R : Set G) → N ≤ normalizer (K : Set G) →
    (∀ a ∈ U, a ^ 2 ∈ R) → (∀ a ∈ U, ∀ b ∈ U, a * b * a⁻¹ * b⁻¹ ∈ R) →
    IsSylowOf 2 U K →
    t ∈ N → v ∈ N → t ^ 2 = 1 → v ^ 2 = 1 → t * v = v * t →
    (¬ ∀ a ∈ U, t * a * t⁻¹ * a⁻¹ ∈ R) → (¬ ∀ a ∈ U, v * a * v⁻¹ * a⁻¹ ∈ R) →
    (¬ ∀ a ∈ U, (t * v) * a * (t * v)⁻¹ * a⁻¹ ∈ R) →
    y ∈ N → v⁻¹ * (y⁻¹ * t * y) ∈ U → (t * v)⁻¹ * (y⁻¹ * v * y) ∈ U →
    (∀ g : G, g * t * g⁻¹ ∈ U ⊔ zpowers t → ∃ u ∈ U, g * t * g⁻¹ = u * t * u⁻¹) →
    (∃ k ∈ K, ¬ ∀ a ∈ U, k * a * k⁻¹ * a⁻¹ ∈ R) →
    (∀ x ∈ K, x * t = t * x → Odd (orderOf x) →
      (∀ a ∈ U, (x * v * x⁻¹ * v⁻¹) * a * (x * v * x⁻¹ * v⁻¹)⁻¹ * a⁻¹ ∈ R) →
      ∀ a ∈ U, x * a * x⁻¹ * a⁻¹ ∈ R) →
    (∀ x ∈ N, x * t = t * x → x ∈ normalizer (X : Set G)) →
    ε ∈ N → ε * t = t * ε → (orderOf ε).Prime →
    (∀ a ∈ U, ε * a * ε⁻¹ * a⁻¹ ∈ R → a ∈ R) →
    (∀ x ∈ K, x * t = t * x → Odd (orderOf x) → (¬ ∀ a ∈ U, x * a * x⁻¹ * a⁻¹ ∈ R) →
      (∀ a ∈ U, (x * ε * x⁻¹ * ε⁻¹) * a * (x * ε * x⁻¹ * ε⁻¹)⁻¹ * a⁻¹ ∈ R) →
      (∀ Y : Subgroup G, R ≤ Y → Y ≤ X → ε ∈ normalizer (Y : Set G) →
        x ∈ normalizer (Y : Set G) → Y = R ∨ Y = X) ∧
      (∀ Y : Subgroup G, X ≤ Y → Y ≤ U → ε ∈ normalizer (Y : Set G) →
        x ∈ normalizer (Y : Set G) → Y = X ∨ Y = U)) →
    False

end SixNineRank

end CFSG.SeitzReduction.RankOne
