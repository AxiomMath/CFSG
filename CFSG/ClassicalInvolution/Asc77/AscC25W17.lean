module

public import CFSG.ClassicalInvolution.Asc77.AscC25W4

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap
open scoped commutatorElement

namespace C25W

section Def

variable (p f : ℕ) [Fact p.Prime]

@[expose] def CentExtMix : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z t u₁ u₂ : G),
    Hyp25 p f Ω K K' W S R R' z t u₁ u₂ →
      ∀ a ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G),
        a * a = 1 → a ≠ 1 → a ≠ z →
        (∀ s ∈ (S : Subgroup G), s * a * s⁻¹ = a ∨ s * a * s⁻¹ = a * z) →
        z ∉ zStarOf (Subgroup.centralizer ({a} : Set G)) →
          ∀ y ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G),
            y * a = a * y → InFour a z (y * y) →
            (∀ s ∈ (S : Subgroup G), InFour a z (s * y * s⁻¹ * y⁻¹)) →
            (∃ x ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G),
              x ∉ Subgroup.zpowers z ∧ z ∉ zStarOf (Subgroup.centralizer ({x} : Set G)) ∧
                z ∈ zStarOf (Subgroup.centralizer ({x * z} : Set G))) →
            InFour a z y

@[expose] def CentExtNoMix : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z t u₁ u₂ : G),
    Hyp25 p f Ω K K' W S R R' z t u₁ u₂ →
      ∀ a ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G),
        a * a = 1 → a ≠ 1 → a ≠ z →
        (∀ s ∈ (S : Subgroup G), s * a * s⁻¹ = a ∨ s * a * s⁻¹ = a * z) →
        z ∉ zStarOf (Subgroup.centralizer ({a} : Set G)) →
          ∀ y ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G),
            y * a = a * y → InFour a z (y * y) →
            (∀ s ∈ (S : Subgroup G), InFour a z (s * y * s⁻¹ * y⁻¹)) →
            ¬ (∃ x ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G),
              x ∉ Subgroup.zpowers z ∧ z ∉ zStarOf (Subgroup.centralizer ({x} : Set G)) ∧
                z ∈ zStarOf (Subgroup.centralizer ({x * z} : Set G))) →
            InFour a z y

theorem centExt_of_parts (hM : CentExtMix p f) (hN : CentExtNoMix p f) : CentExt p f := by
  intro G _ _ _ Ω K K' W S R R' z t u₁ u₂ hyp a haA ha2 ha1 haz hconj hbad y hyA hya hy2 hyc
  by_cases hm : ∃ x ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G),
      x ∉ Subgroup.zpowers z ∧ z ∉ zStarOf (Subgroup.centralizer ({x} : Set G)) ∧
        z ∈ zStarOf (Subgroup.centralizer ({x * z} : Set G))
  · exact hM G Ω K K' W S R R' z t u₁ u₂ hyp a haA ha2 ha1 haz hconj hbad y hyA hya hy2 hyc hm
  · exact hN G Ω K K' W S R R' z t u₁ u₂ hyp a haA ha2 ha1 haz hconj hbad y hyA hya hy2 hyc hm

end Def

end C25W

end CFSG.ClassicalInvolution.Asc77
