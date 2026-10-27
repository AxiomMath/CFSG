module

public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.Vocab

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec13

open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

@[expose] def fixSec (x : G) (N M : Subgroup G) : Set G :=
  {g | g ∈ M ∧ x * g * x⁻¹ * g⁻¹ ∈ N}

@[expose] def FreeSec2 (x : G) (N M : Subgroup G) : Prop :=
  N ≤ M ∧ (∀ a ∈ M, ∀ b ∈ M, ⁅a, b⁆ ∈ N) ∧ (∀ a ∈ M, a * a ∈ N) ∧
    (∀ g ∈ N, x * g * x⁻¹ ∈ N) ∧ (∀ g ∈ M, x * g * x⁻¹ ∈ M) ∧
    Nat.card (fixSec x N M) ^ 2 = Nat.card M * Nat.card N

@[expose] def IsExtremal2 (P : Subgroup G) (y : G) : Prop :=
  y ∈ P ∧ Sylow2In (P ⊓ centralizer ({y} : Set G)) (centralizer ({y} : Set G))

@[expose] def IG_10_31 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (P : Subgroup G) (x : G) (n : ℕ) (Pi : ℕ → Subgroup G),
    x * x = 1 → x ∈ normalizer (P : Set G) → x ∉ P → Pi 0 = ⊥ → Pi n = P →
    (∀ i < n, FreeSec2 x (Pi i) (Pi (i + 1))) →
    ∀ p ∈ P, (p * x) * (p * x) = 1 → ∃ q ∈ P, p * x = q * x * q⁻¹

@[expose] def IG_15_15 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (P Q : Subgroup G) (u : G), Sylow2In P ⊤ → Q ≤ P →
    (∀ g ∈ P, ∀ q ∈ Q, g * q * g⁻¹ ∈ Q) → Q ≠ P → (∃ g ∈ P, P = Q ⊔ zpowers g) →
    u ∈ P → u ∉ Q → u * u = 1 →
    (∀ w : G, IsExtremal2 P (w * u * w⁻¹) → w * u * w⁻¹ ∈ Q ∨ ∃ q ∈ Q, w * u * w⁻¹ = q * u) →
    (∃ (N : Subgroup G) (_ : N.Normal), IsCyclic (G ⧸ N) ∧ IsPGroup 2 (G ⧸ N) ∧ u ∉ N) ∨
      ∃ w : G, w * u * w⁻¹ ∈ Q ∧ IsExtremal2 P (w * u * w⁻¹) ∧
        ∀ c ∈ P ⊓ centralizer ({u} : Set G), w * c * w⁻¹ ∈ P ⊓ centralizer ({w * u * w⁻¹} : Set G)

@[expose] def IG_16_20 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (P A : Subgroup G), Sylow2In P ⊤ → A ≤ P →
    (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) →
    (∀ a ∈ A, ∀ g : G, g * a * g⁻¹ ∈ P → g * a * g⁻¹ ∈ A) →
    ∀ u ∈ P, ∀ g : G, g * u * g⁻¹ ∈ P → ∃ n ∈ normalizer (A : Set G), n * u * n⁻¹ = g * u * g⁻¹

@[expose] def IV2_2_18 : Prop :=
  ∀ (E : Type) [Group E] [Finite E], Nonempty (E ≃* E24) →
    ∀ (X S : Subgroup (MulAut E)), Sylow2In S X → IsFourGroup S →
      Nat.card {e : E // ∀ s ∈ S, s e = e} = 2 →
      ∀ x ∈ S, x ≠ 1 →
        Nonempty (↥(X ⊓ centralizer ({x} : Set (MulAut E))) ≃*
          (Multiplicative (ZMod 2) × Equiv.Perm (Fin 3))) →
        ¬ ∀ u ∈ X, ∀ v ∈ X, u ≠ 1 → u * u = 1 → v ≠ 1 → v * v = 1 → ∃ g ∈ X, g * u * g⁻¹ = v

end CFSG.GH74.GLS.Stage1.Thm6.Sec13
