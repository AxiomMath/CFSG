module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S25F1

public section

namespace CFSG.ClassicalInvolution.Hat2A7S

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected

section Types

variable {G : Type} [Group G]

@[expose] def fixImage (K : Subgroup G) (a : G) : Subgroup (Hat2A7.OddQuot K) :=
  ((K ⊓ Subgroup.centralizer ({a} : Set G)).subgroupOf K).map
    (QuotientGroup.mk' (classicalInvolutionOddCore ↥K))

@[expose] def FixDiv5 (K : Subgroup G) (a : G) : Prop :=
  5 ∣ Nat.card (fixImage K a)

theorem mem_fixImage {K : Subgroup G} {a : G} {q : Hat2A7.OddQuot K} :
    q ∈ fixImage K a ↔ ∃ x : ↥K, (x : G) ∈ Subgroup.centralizer ({a} : Set G) ∧
      (x : Hat2A7.OddQuot K) = q := by
  unfold fixImage
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx.2, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, ⟨x.2, hx⟩, rfl⟩

end Types

section Statements

@[expose] def A7NoFFz5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z t u₁ u₂ : G),
    Hyp25A7 Ω K K' W S R R' z t u₁ u₂ → ∀ a ∈ (S : Subgroup G), a * a = 1 →
      IsFAut R a → IsFAut R' a → z ∉ zStarOf (Subgroup.centralizer ({a} : Set G)) →
        FixDiv5 K' a → False

@[expose] def A7NoFFz3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z t u₁ u₂ : G),
    Hyp25A7 Ω K K' W S R R' z t u₁ u₂ → ∀ a ∈ (S : Subgroup G), a * a = 1 →
      IsFAut R a → IsFAut R' a → z ∉ zStarOf (Subgroup.centralizer ({a} : Set G)) →
        ¬ FixDiv5 K' a → False

theorem a7NoFFz_of_5_3 (h5 : A7NoFFz5) (h3 : A7NoFFz3) : A7NoFFz := by
  intro G _ _ _ Ω K K' W S R R' z t u₁ u₂ hyp a haS ha2 hFa hFa' hZ
  by_cases hd : FixDiv5 K' a
  · exact h5 G Ω K K' W S R R' z t u₁ u₂ hyp a haS ha2 hFa hFa' hZ hd
  · exact h3 G Ω K K' W S R R' z t u₁ u₂ hyp a haS ha2 hFa hFa' hZ hd

end Statements

end CFSG.ClassicalInvolution.Hat2A7S
