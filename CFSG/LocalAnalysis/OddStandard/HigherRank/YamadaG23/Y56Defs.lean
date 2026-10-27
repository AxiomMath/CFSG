module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YCtx

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

abbrev e4Q (s : Setting3 G L) : Subgroup G := s.fr.E ⊔ zpowers s.t

abbrev e4X (s : Setting3 G L) : Subgroup G :=
  normalizer ((s.fr.E ⊔ zpowers s.t : Subgroup G) : Set G)

abbrev e4Y (s : Setting3 G L) : Subgroup G := centIn (e4X s) s.fr.E

abbrev e4X0 (s : Setting3 G L) : Subgroup G := centIn s.H s.fr.E

abbrev e4N (s : Setting3 G L) : Subgroup G := normIn s.H s.fr.E

theorem e4_C4_eq (s : Setting3 G L) : C4 s = pCoreOf 2 ⁅e4Y s, e4N s⁆ ⊔ e4Q s := rfl

abbrev y56e0 (s : Setting3 G L) : G := s.fr.a₁ * s.fr.b₁ * s.fr.a₂

abbrev y56v0 (s : Setting3 G L) : G := s.fr.b₁ * s.fr.b₂

@[expose] def IsY0 (s : Setting3 G L) (y₀ : G) : Prop :=
  y₀ ∈ s.C₂ ∧ (∀ f ∈ s.fr.E, y₀ * f * y₀⁻¹ = f) ∧ y₀ * s.t * y₀⁻¹ = y56v0 s * s.t

@[expose] def IsC4Cand (s : Setting3 G L) (d : G) (M : Subgroup G) : Prop :=
  e4Q s ≤ M ∧ M ≤ e4Y s ∧ (∀ n ∈ normIn L s.fr.E, ∀ m ∈ M, n * m * n⁻¹ ∈ M) ∧
    M ⊓ e4X0 s = e4Q s ∧ M ⊔ e4X0 s = e4Y s ∧ d ∈ M

end CFSG.OddStandard.HigherRank.YamadaG23
