module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S25F0
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7M8

public section

namespace CFSG.ClassicalInvolution.Hat2A7S

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected

section Statements

@[expose] def A7Mix25 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z t u₁ u₂ : G),
    Hyp25A7 Ω K K' W S R R' z t u₁ u₂ → ∀ a ∈ (S : Subgroup G), a * a = 1 →
      IsFAut R' a →
        (∃ r ∈ R, ∀ x ∈ R, (r⁻¹ * a) * x = x * (r⁻¹ * a)) ∨
          ∃ r ∈ R, (a * r) * (a * r) = 1 ∧ IsFAut R (a * r)

@[expose] def A7NoFFz : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z t u₁ u₂ : G),
    Hyp25A7 Ω K K' W S R R' z t u₁ u₂ → ∀ a ∈ (S : Subgroup G), a * a = 1 →
      IsFAut R a → IsFAut R' a → z ∉ zStarOf (Subgroup.centralizer ({a} : Set G)) → False

end Statements

section Reductions

theorem a7_false_of_ff (h11 : A7C25_11) (hno : A7NoFFz) {G : Type} [Group G] [Finite G]
    [IsSimpleGroup G] {Ω : Set (Subgroup G)} {K K' W : Subgroup G} {S : Sylow 2 G}
    {R R' : Subgroup G} {z t u₁ u₂ : G} (hyp : Hyp25A7 Ω K K' W S R R' z t u₁ u₂) {a : G}
    (haS : a ∈ (S : Subgroup G)) (ha2 : a * a = 1) (hFa : IsFAut R a) (hFa' : IsFAut R' a) :
    False := by
  by_cases hZ : z ∈ zStarOf (Subgroup.centralizer ({a} : Set G))
  · exact Hat2A7M.Asc77.C25V.false_of_zStar_ff (mirror_c25_11 h11) hyp.toMirror haS ha2 hFa hFa'
      hZ
  · exact hno G Ω K K' W S R R' z t u₁ u₂ hyp a haS ha2 hFa hFa' hZ

theorem mirror_mix25 (h : A7Mix25) :
    ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
      (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z t u₁ u₂ : G),
      Hat2A7M.Asc77.Hyp25 Ω K K' W S R R' z t u₁ u₂ → ∀ a ∈ (S : Subgroup G), a * a = 1 →
        IsFAut R' a →
          (∃ r ∈ R, ∀ x ∈ R, (r⁻¹ * a) * x = x * (r⁻¹ * a)) ∨
            ∃ r ∈ R, (a * r) * (a * r) = 1 ∧ IsFAut R (a * r) :=
  fun G _ _ _ Ω K K' W S R R' z t u₁ u₂ hyp a haS ha2 hF' =>
    h G Ω K K' W S R R' z t u₁ u₂ (Hyp25A7.of_mirror hyp) a haS ha2 hF'

theorem a7C25_16inv_of_noffz (h11 : A7C25_11) (hmix : A7Mix25) (hno : A7NoFFz) :
    A7C25_16inv := by
  intro G _ _ _ Ω K K' W S R R' z t u₁ u₂ hyp a haS ha2 hF'
  rcases mirror_mix25 hmix G Ω K K' W S R R' z t u₁ u₂ hyp.toMirror a haS ha2 hF' with
    hin | ⟨r, hrR, ha'2, hFa'⟩
  · obtain ⟨e, heS, he2, hFe, hFe'⟩ := Hat2A7M.Asc77.C25V.exists_ff_of_inner (mirror_c25_11 h11)
      hyp.toMirror haS ha2 hF' hin
    exact (a7_false_of_ff h11 hno hyp heS he2 hFe hFe').elim
  · obtain ⟨t₀, h₀⟩ := Hat2A7M.Asc77.T7T.exists_hyp25T hyp.toMirror
    have ha'S : a * r ∈ (S : Subgroup G) := S.mul_mem haS (h₀.hRS hrR)
    have hF'a' : IsFAut R' (a * r) :=
      T7U.isFAut_mul_of_centralizes (fun x hx => h₀.hcomm r hrR x hx) hF'
    exact (a7_false_of_ff h11 hno hyp ha'S ha'2 hFa' hF'a').elim

end Reductions

end CFSG.ClassicalInvolution.Hat2A7S
