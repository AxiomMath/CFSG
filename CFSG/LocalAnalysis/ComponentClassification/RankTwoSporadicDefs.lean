module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoStandardDefs

public section

namespace CFSG.ComponentClassification.RankTwoSporadic

open Subgroup CFSG.Open
open scoped commutatorElement

variable {W : Type*} [Group W]

@[expose] def centDer (X : Subgroup W) (t : W) : Subgroup W :=
  ⁅X ⊓ centralizer ({t} : Set W), X ⊓ centralizer ({t} : Set W)⁆

@[expose] def gammaE (X E : Subgroup W) : Subgroup W :=
  ⨆ t ∈ E, ⨆ (_ : t ≠ 1), centDer X t

@[expose] def nE (X E : Subgroup W) : Subgroup W :=
  ⁅E, gammaE X E⁆

@[expose] def YWitness (X E : Subgroup W) : Prop :=
  (∃ w ∈ nE X E, 4 ∣ orderOf w) ∨
    ∃ P : Subgroup W, P ≤ nE X E ∧ IsPGroup 2 P ∧ Nat.card ↥(E ⊓ X) < Nat.card P

@[expose] def YCensus (X : Subgroup W) (Exc : Subgroup W → Prop) : Prop :=
  ∀ E : Subgroup W, IsElemAbelian 2 E → 4 ≤ Nat.card E → ¬ Exc E → YWitness X E

@[expose] def PWitness (X E : Subgroup W) : Prop :=
  ∃ P : Subgroup W, P ≤ gammaE X E ∧ ⁅P, P⁆ = P ∧ ¬ E ≤ centralizer (P : Set W) ∧
    ∃ x ∈ P, IsPGroup 2 (zpowers x) ∧ P ≤ closure {y | ∃ p ∈ P, y = p * x ^ 2 * p⁻¹}

@[expose] def YCensus17 (X : Subgroup W) (Exc : Subgroup W → Prop) : Prop :=
  ∀ E : Subgroup W, IsElemAbelian 2 E → 4 ≤ Nat.card E → ¬ Exc E → YWitness X E ∨ PWitness X E

@[expose] def UWitness (X E : Subgroup W) : Prop :=
  ∃ s ∈ E, s ≠ 1 ∧ (∃ t ∈ E, t ≠ 1 ∧ ∃ c ∈ X, c * t = t * c ∧ IsPGroup 2 (zpowers c) ∧
      ∃ v ∈ E, ⁅v, c⁆ = s) ∧
    ∃ P : Subgroup W, P ≤ ⁅X ⊓ centralizer (E : Set W), X ⊓ centralizer (E : Set W)⁆ ∧
      ⁅P, P⁆ = P ∧ s ∈ P

@[expose] def YCensus17U (X : Subgroup W) (Exc : Subgroup W → Prop) : Prop :=
  ∀ E : Subgroup W, IsElemAbelian 2 E → 4 ≤ Nat.card E → ¬ Exc E →
    YWitness X E ∨ PWitness X E ∨ UWitness X E

@[expose] def OddMultiplier (X₀ : Type*) [Group X₀] : Prop :=
  ∀ (A : Type) [Group A] [Finite A], commutator A = ⊤ → Nonempty (A ⧸ center A ≃* X₀) →
    Odd (Nat.card (center A))

structure AutModel (X₀ : Type*) [Group X₀] (W : Type*) [Group W] (X : Subgroup W) : Prop where
  normal : X.Normal
  centralizer_eq_bot : centralizer (X : Set W) = ⊥
  nonempty_mulEquiv : Nonempty (↥X ≃* X₀)
  exists_conj : ∀ α : MulAut ↥X, ∃ w : W, ∀ x : ↥X, ((α x : ↥X) : W) = w * x * w⁻¹

structure IsActionHom {G : Type*} [Group G] (A : Subgroup G) (X : Subgroup W)
    (ψ : normalizer (A : Set G) →* W) : Prop where
  map_mem : ∀ (a : G) (ha : a ∈ A), ψ ⟨a, le_normalizer ha⟩ ∈ X
  exists_eq : ∀ x ∈ X, ∃ (a : G) (ha : a ∈ A), ψ ⟨a, le_normalizer ha⟩ = x
  eq_one_iff : ∀ n : normalizer (A : Set G), ψ n = 1 ↔ (n : G) ∈ centralizer (A : Set G)

@[expose] def SporadicCaseOdd (s : TauCeti.SporadicName) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G), RankTwoStandard.RankTwoHyp G A →
    standardComponentOddCore G = ⊥ →
      ¬ Blueprint.NativeSporadic.IsSporadic (RankTwoStandard.rankTwoQuot A) s

end CFSG.ComponentClassification.RankTwoSporadic
