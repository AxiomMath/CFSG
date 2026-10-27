module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1Stage

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup

@[expose] def U3C1TorusFpf {G : Type*} [Group G] (L T : Subgroup G) (d : G) : Prop :=
  ∃ m : ℕ, (∀ b ∈ szA₁ (szT₁ L T), d ^ m * b * (d ^ m)⁻¹ = b) ∧
    ∀ y ∈ szT₁ L T, y⁻¹ * (d ^ m * y * (d ^ m)⁻¹) ∈ szA₁ (szT₁ L T) → y ∈ szA₁ (szT₁ L T)

@[expose] def U3C1TorusScalar {G : Type*} [Group G] (L T : Subgroup G) (f : ℕ) (d : G) : Prop :=
  ∃ (E : Type) (_ : Field E) (_ : Finite E) (_ : CharP E 2) (σ : E →+* E),
    Nat.card E = (2 ^ f) ^ 2 ∧ (∀ x, σ x = x ^ (2 ^ f)) ∧
    ∃ u v : G → E, U3RootCoords (szT₁ L T) σ u v ∧
      (∀ y ∈ szT₁ L T, (y ∈ szA₁ (szT₁ L T) ↔ u y = 0)) ∧
      ∃ μ : E, μ ≠ 0 ∧ orderOf μ = ((2 ^ f) ^ 2 - 1) / Nat.gcd 3 (2 ^ f + 1) ∧
        ∀ y ∈ szT₁ L T, u (d * y * d⁻¹) = μ * u y

@[expose] def U3C1TorusFullInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (f : ℕ) (t : G) (T R₂ : Subgroup G),
    U3Start G L f t T → (∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) →
    U3R2 G L (szT₁ L T) R₂ t f →
    ∃ d : G, Odd (orderOf d) ∧ d ∈ normalizer (R₂ : Set G) ∧
      d ∈ normalizer (szT₁ L T : Set G) ∧ d * t = t * d ∧ U3C1TorusFpf L T d ∧
      U3C1TorusScalar L T f d ∧
      ∃ (K : Type) (_ : Field K) (_ : Fintype K) (_ : CharP K 2) (v : G → K) (μ : K),
        Fintype.card K = 2 ^ f ∧ U3A₁Coords (szA₁ (szT₁ L T)) d v μ ∧
          ∀ w : K, w ≠ 0 → ∃ m : ℕ, μ ^ m = w

end CFSG.SeitzReduction.RankOne
