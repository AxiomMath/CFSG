module

public import CFSG.ClassicalInvolution.Asc77.AscC25V11
public import CFSG.ClassicalInvolution.Asc77.AscC25V3
public import CFSG.ClassicalInvolution.Asc77.AscT7TC15

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.C25V

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped MatrixGroups commutatorElement

section Defs

variable (p f : ℕ) [Fact p.Prime]


@[expose] def Fus25 : Prop :=
  p ^ f ≠ 9 → ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z t u₁ u₂ : G),
    Hyp25 p f Ω K K' W S R R' z t u₁ u₂ → ∀ a ∈ (S : Subgroup G), a * a = 1 → IsFAut R' a →
      (¬ ∃ c : G, c * a = a * c ∧ c * z = z * c ∧ conjSub c K' = K) →
        ∀ x : G, x⁻¹ * a * x ∈ Subgroup.centralizer ({z} : Set G) →
          ∃ c ∈ Subgroup.centralizer ({z} : Set G), x⁻¹ * a * x = c⁻¹ * a * c

@[expose] def FieldStrong25 : Prop :=
  p ^ f ≠ 9 → ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z t u₁ u₂ : G),
    Hyp25 p f Ω K K' W S R R' z t u₁ u₂ → ∀ a ∈ (S : Subgroup G), a * a = 1 → IsFAut R' a →
      ∀ (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (haK : a ∈ Subgroup.normalizer (K : Set G))
        (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, GaloisField p f)),
        fieldChar hp hq e ⟨a, haK⟩ ≠ 1 →
          ∃ r ∈ R, (a * r) * (a * r) = 1 ∧ IsFAut R (a * r)

theorem mix25_of_fusion (h9 : p ^ f ≠ 9) (hfus : Fus25 p f) (hfs : FieldStrong25 p f) :
    Mix25 p f := by
  intro G _ _ _ Ω K K' W S R R' z t u₁ u₂ hyp a haS ha2 hF'
  obtain ⟨t', h⟩ := T7T.exists_hyp25T hyp
  have hp : p ≠ 2 := h.hp
  have hq : 5 ≤ p ^ f := h.hs.stand.five
  have haK : a ∈ Subgroup.normalizer (K : Set G) :=
    mem_normalizer_iff_conjSub_eq.mpr (fix_of_isFAut h haS hF').2.2.1
  obtain ⟨e⟩ := h.hΩ.nonempty_equiv_sl2 h.hK
  by_cases hχ : fieldChar hp hq e ⟨a, haK⟩ = 1
  · exfalso
    have hnoswap : ¬ ∃ c : G, c * a = a * c ∧ c * z = z * c ∧ conjSub c K' = K := by
      rintro ⟨c, hca, hcz, hcK⟩
      exact fieldChar_ne_one_of_swap h hp hq e ha2 hF' hca hcz hcK haK hχ
    exact false_of_mix_fusion h hp hq e haS ha2 hF' haK hχ
      (hfus h9 G Ω K K' W S R R' z t u₁ u₂ hyp a haS ha2 hF' hnoswap)
  · exact Or.inr (hfs h9 G Ω K K' W S R R' z t u₁ u₂ hyp a haS ha2 hF' hp hq haK e hχ)

end Defs

end CFSG.ClassicalInvolution.Asc77.C25V
