module

public import CFSG.GH74.GLS.Stage1.Thm6.Prelude

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec12

open Subgroup CFSG.GH74.GLS.Stage1.Thm6

@[expose] def IsExtremal {X : Type*} [Group X] (P : Subgroup X) (y : X) : Prop :=
  IsSylow2In (P ⊓ Subgroup.centralizer ({y} : Set X)) (Subgroup.centralizer ({y} : Set X))

@[expose] def IG_15_3 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsSimpleGroup X → (∃ a b : X, a * b ≠ b * a) →
    ∀ P : Subgroup X, IsSylow2In P ⊤ → ∀ z ∈ P, z * z = 1 → z ≠ 1 → (∀ t ∈ P, z * t = t * z) →
      ∃ g : X, g⁻¹ * z * g ∈ P ∧ g⁻¹ * z * g ≠ z

@[expose] def IG_16_2 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (P : Subgroup X), IsSylow2In P ⊤ →
    ∀ a b : X, a ∈ P → b ∈ P → (∀ t ∈ P, a * t = t * a) → (∀ t ∈ P, b * t = t * b) →
      (∃ g : X, g⁻¹ * a * g = b) → ∃ n ∈ Subgroup.normalizer (P : Set X), n⁻¹ * a * n = b

@[expose] def IG_15_15 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (P Q : Subgroup X) (u : X),
    IsSylow2In P ⊤ → Q ≤ P → (∀ t ∈ P, ∀ q ∈ Q, t * q * t⁻¹ ∈ Q) → Q ≠ P →
    (∃ b ∈ P, ∀ t ∈ P, ∃ k : ℤ, (b ^ k)⁻¹ * t ∈ Q) →
    u ∈ P → u ∉ Q → (∀ v ∈ P, v ∉ Q → orderOf u ≤ orderOf v) →
    (∀ y ∈ P, (∃ g : X, g⁻¹ * u * g = y) → IsExtremal P y → y ∈ Q ∨ u⁻¹ * y ∈ Q) →
    (∃ (N : Subgroup X) (_ : N.Normal), IsCyclic (X ⧸ N) ∧ IsPGroup 2 (X ⧸ N) ∧ u ∉ N) ∨
    ∃ g : X, g⁻¹ * u * g ∈ Q ∧ IsExtremal P (g⁻¹ * u * g) ∧
      ∀ c ∈ P ⊓ Subgroup.centralizer ({u} : Set X),
        g⁻¹ * c * g ∈ P ⊓ Subgroup.centralizer ({g⁻¹ * u * g} : Set X)

end CFSG.GH74.GLS.Stage1.Thm6.Sec12
