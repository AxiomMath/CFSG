module

public import CFSG.ClassicalInvolution.Asc77.WP2Thm7c

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

variable (p f : ℕ) [Fact p.Prime]

structure Hyp24Data {G : Type} [Group G] [Finite G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z u : G) : Prop where
  hW : W ∈ WSet Ω
  hzW : z ∈ W
  hS4 : MuIsoS4 Ω W
  hZ : W ⊓ centerIn (Subgroup.normalizer (W : Set G)) = ⊥
  hWS : W ≤ (S : Subgroup G)
  hR : R ∈ RSet Ω ∧ R ≤ K ∧ R ≤ (S : Subgroup G)
  hR' : R' ∈ RSet Ω ∧ R' ≤ K' ∧ R' ≤ (S : Subgroup G)
  hu : u ∈ K ⊔ K' ∧ u ∈ W ∧ u * u = 1 ∧ u ≠ 1 ∧ u ≠ z

structure Hyp25Data {G : Type} [Group G] [Finite G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z t u₁ u₂ : G) : Prop where
  hW : W ∈ WSet Ω
  hzW : z ∈ W
  hE4 : MuIsoE4 Ω W
  hR : R ∈ RSet Ω ∧ R ≤ K ∧ R ≤ (S : Subgroup G)
  hR' : R' ∈ RSet Ω ∧ R' ≤ K' ∧ R' ≤ (S : Subgroup G)
  hRS : ∀ X ∈ RSet Ω, X ≤ (S : Subgroup G) → X = R ∨ X = R'
  hzS : ∀ s ∈ (S : Subgroup G), s * z = z * s
  ht : t ∈ (S : Subgroup G) ∧ t ≠ z ∧ ∃ g : G, g * z * g⁻¹ = t
  hu₁ : u₁ ∈ R ∧ orderOf u₁ = 4 ∧ ∀ r ∈ R, r * u₁ * r⁻¹ ∈ Subgroup.zpowers u₁
  hu₂ : u₂ ∈ R' ∧ orderOf u₂ = 4 ∧ ∀ r ∈ R', r * u₂ * r⁻¹ ∈ Subgroup.zpowers u₂

variable {p f}

section Conversions

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K K' W : Subgroup G}
  {S : Sylow 2 G} {R R' : Subgroup G} {z u t u₁ u₂ : G}

theorem Hyp24.data (h : Hyp24 p f Ω K K' W S R R' z u) : Hyp24Data Ω K K' W S R R' z u where
  hW := h.hW
  hzW := h.hzW
  hS4 := h.hS4
  hZ := h.hZ
  hWS := h.hWS
  hR := h.hR
  hR' := h.hR'
  hu := h.hu

theorem Hyp24Data.hyp24 (h : Hyp24Data Ω K K' W S R R' z u) (hs : Hyp23 p f Ω K K' z) :
    Hyp24 p f Ω K K' W S R R' z u where
  std := hs
  hW := h.hW
  hzW := h.hzW
  hS4 := h.hS4
  hZ := h.hZ
  hWS := h.hWS
  hR := h.hR
  hR' := h.hR'
  hu := h.hu

theorem Hyp25.data (h : Hyp25 p f Ω K K' W S R R' z t u₁ u₂) :
    Hyp25Data Ω K K' W S R R' z t u₁ u₂ where
  hW := h.hW
  hzW := h.hzW
  hE4 := h.hE4
  hR := h.hR
  hR' := h.hR'
  hRS := h.hRS
  hzS := h.hzS
  ht := h.ht
  hu₁ := h.hu₁
  hu₂ := h.hu₂

theorem Hyp25Data.hyp25 (h : Hyp25Data Ω K K' W S R R' z t u₁ u₂) (hs : Hyp23 p f Ω K K' z) :
    Hyp25 p f Ω K K' W S R R' z t u₁ u₂ where
  std := hs
  hW := h.hW
  hzW := h.hzW
  hE4 := h.hE4
  hR := h.hR
  hR' := h.hR'
  hRS := h.hRS
  hzS := h.hzS
  ht := h.ht
  hu₁ := h.hu₁
  hu₂ := h.hu₂

end Conversions

namespace T7C

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

theorem isSylow2In_of_mem_RSet_of_le (hp : p ≠ 2) (hΩ : HypOmegaMod p f Ω) {K R : Subgroup G}
    (hK : K ∈ Ω) (hR : R ∈ RSet Ω) (hRK : R ≤ K) : IsSylow2In R K := by
  obtain ⟨J, hJ, hRJ⟩ := exists_isSylow2In_of_mem_RSet hR
  by_cases hJK : J = K
  · exact hJK ▸ hRJ
  · exfalso
    have h1 := hΩ.card_le_two_of_le_inf hJ hK hJK hRJ.2.1 hRJ.1 hRK
    have h2 := hΩ.eight_le_of_mem_RSet hp hR
    omega

end T7C

@[expose] def dGrp24 {G : Type} [Group G] (K : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G)
    (g : G) : Subgroup G :=
  (Subgroup.centralizer (R : Set G) ⊓ Subgroup.normalizer ((conjSub g⁻¹ K : Subgroup G) : Set G) ⊓
    (S : Subgroup G)) ⊓ Subgroup.centralizer (R' : Set G)

end CFSG.ClassicalInvolution.Asc77
