module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76Setting

public section

namespace CFSG.ComponentClassification.Sol76

open CFSG Subgroup CFSG.ComponentClassification.FooteLit

abbrev Thm13Ambient : Type 1 := ∀ (G : Type) [Group G] [Finite G], Prop

@[expose] def Lemma316InputFor (𝒜 : Thm13Ambient) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], 𝒜 G → ∀ N : Subgroup G, IsSolomonChoice N →
    solomonKStarOf (normalizer (solomonKStarOf N : Set G)) = solomonKStarOf N ∧
      ∀ K ∈ kStarComponents N, ∀ b ∈ K, orderOf b = 2 →
        centralizer ({b} : Set G) ≤ normalizer (solomonKStarOf N : Set G)

@[expose] def Lemma316Input : Prop := Lemma316InputFor (fun G _ _ => Thm13Below G)

@[expose] def Lemma313InputFor (𝒜 : Thm13Ambient) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], 𝒜 G → ∀ N : Subgroup G, IsSolomonChoice N →
    ∀ M : Subgroup G, solomonKStarOf M = solomonKStarOf N →
      M = normalizer (solomonKStarOf N : Set G) →
      (∀ K ∈ kStarComponents N, ∀ s ∈ K, orderOf s = 2 → centralizer ({s} : Set G) ≤ M) →
      (∀ K ∈ kStarComponents N, ∀ K' ∈ kStarComponents N, ∀ t g : G, t ∈ M → g⁻¹ * t * g ∈ M →
          (∃ k : ℕ, t ^ (2 ^ k) = 1) → t ∉ center G →
          (∀ a ∈ K, t⁻¹ * a⁻¹ * t * a ∈ oddCoreIn (solomonKStarOf N)) →
          (∀ a ∈ K', (g⁻¹ * t * g)⁻¹ * a⁻¹ * (g⁻¹ * t * g) * a ∈ oddCoreIn (solomonKStarOf N)) →
          g ∈ M) ∧
        ∀ K ∈ kStarComponents N, ∀ (g : G) (X : Subgroup G), X ≤ conjugate M g →
          (∀ a ∈ K, ∃ x ∈ X, ∃ o ∈ oddCoreIn (solomonKStarOf N), a = x * o) → g ∈ M

@[expose] def Lemma313Input : Prop := Lemma313InputFor (fun G _ _ => Thm13Below G)

end CFSG.ComponentClassification.Sol76
