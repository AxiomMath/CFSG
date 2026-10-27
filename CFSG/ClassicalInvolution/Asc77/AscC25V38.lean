module

public import CFSG.ClassicalInvolution.Asc77.AscC25V37

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.C25V

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Disconnected.AschTight.S1911
open scoped MatrixGroups

section Defs

variable (p f : ℕ) [Fact p.Prime]


@[expose] def G1_25 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z t u₁ u₂ t' : G),
    T7F2.Hyp25T p f Ω K K' W S R R' z t u₁ u₂ t' → p ^ f ≠ 9 → ∀ a : G, a ∈ (S : Subgroup G) →
      a * a = 1 → IsFAut R' a → a * t' = t' * a →
      z ∉ zStarOf (Subgroup.centralizer ({a} : Set G)) →
        ∀ (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
          (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, GaloisField p f)) (d : G)
          (hdK : d ∈ Subgroup.normalizer (K : Set G)), d * z = z * d → d * a = a * d →
          ∀ (hd' : t' * d * t' ∈ Subgroup.normalizer (K : Set G)),
            Odd (orderOf (fieldChar hp hq e ⟨d, hdK⟩ * (fieldChar hp hq e ⟨t' * d * t', hd'⟩)⁻¹))

@[expose] def G1Omega6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z t u₁ u₂ t' : G),
    T7F2.Hyp25T p f Ω K K' W S R R' z t u₁ u₂ t' → p ^ f ≠ 9 → ∀ a : G, a ∈ (S : Subgroup G) →
      a * a = 1 → IsFAut R' a → a * t' = t' * a →
      ∀ (e₀ : ℕ), 5 ≤ p ^ e₀ → ∀ hzA : z ∈ Subgroup.centralizer ({a} : Set G),
        IsClassicalMember p e₀ (perfectCoreIn K' a) ⟨z, hzA⟩ →
        SectionOrthType p e₀ (conjFamily (perfectCoreIn K' a)) (conjGen (perfectCoreIn K' a))
          6 (!piSign p e₀) →
        ∀ (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
          (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, GaloisField p f)) (d : G)
          (hdK : d ∈ Subgroup.normalizer (K : Set G)), d * z = z * d → d * a = a * d →
          ∀ (hd' : t' * d * t' ∈ Subgroup.normalizer (K : Set G)),
            Odd (orderOf (fieldChar hp hq e ⟨d, hdK⟩ * (fieldChar hp hq e ⟨t' * d * t', hd'⟩)⁻¹))

end Defs

section Proof

variable {p f : ℕ} [Fact p.Prime]


theorem g1_25_of_omega6 (h6 : G1Omega6 p f) : G1_25 p f := by
  intro G _ _ _ Ω K K' W S R R' z t u₁ u₂ t' h h9 a haS ha2 hF' hat hZ hp hq e d hdK hdz hda hd'
  obtain ⟨e₀, hfe, h5, hzA, hL, hcases⟩ := fs_typed h h9 haS ha2 hF' hat
  rcases hcases with hz | h5' | h6'
  · exact absurd hz hZ
  · exact g1_omega5 h h9 haS ha2 hF' hat h5 hzA hL h5' hp hq e hdK hdz hda hd'
  · exact h6 G Ω K K' W S R R' z t u₁ u₂ t' h h9 a haS ha2 hF' hat e₀ h5 hzA hL h6' hp hq e d hdK
      hdz hda hd'

end Proof

end CFSG.ClassicalInvolution.Asc77.C25V
