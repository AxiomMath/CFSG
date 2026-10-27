module

public import Mathlib.GroupTheory.OrderOfElement

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.LieOdd

variable (S : Type) [Group S]

@[expose] def U43F1 : Prop :=
  ∀ u : S, orderOf u = 2 → ∃ g : S, 5 < orderOf (u * (g * u * g⁻¹))

@[expose] def U43F2 : Prop :=
  ∀ a b : S, orderOf a = 2 → orderOf b = 2 → b ≠ a → Commute a b →
    ∃ c : S, Commute c a ∧ ¬ Commute b (c * b * c⁻¹)

variable {S} in
@[expose] def IsSmallAut (ψ : MulAut S) : Prop :=
  ∀ g : S, orderOf (ψ * (MulAut.conj g * ψ * (MulAut.conj g)⁻¹)) ≤ 5

@[expose] def U43F3 : Prop :=
  ∀ ψ₁ ψ₂ : MulAut S, orderOf ψ₁ = 2 → orderOf ψ₂ = 2 → Commute ψ₁ ψ₂ →
    ψ₁ ∉ (MulAut.conj : S →* MulAut S).range → ψ₂ ∉ (MulAut.conj : S →* MulAut S).range →
    ψ₁ * ψ₂ ∉ (MulAut.conj : S →* MulAut S).range →
    IsSmallAut ψ₁ → IsSmallAut ψ₂ → IsSmallAut (ψ₁ * ψ₂) →
    (∀ c : S, ψ₁ c = c ↔ ψ₂ c = c) → (∀ c : S, ψ₁ c = c ↔ (ψ₁ * ψ₂) c = c) → False

@[expose] def AutTwoRankLE (m : ℕ) : Prop :=
  ∀ B : Subgroup (MulAut S), (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) → (∀ x ∈ B, x * x = 1) →
    Nat.card B ≤ 2 ^ m

@[expose] def OutElemIndexLE (k : ℕ) : Prop :=
  ∀ B : Subgroup (MulAut S), (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) → (∀ x ∈ B, x * x = 1) →
    Nat.card B ≤ k * Nat.card ↥(B ⊓ (MulAut.conj : S →* MulAut S).range)

end CFSG.HardMathSupport.Meierfrankenfeld.LieOdd
