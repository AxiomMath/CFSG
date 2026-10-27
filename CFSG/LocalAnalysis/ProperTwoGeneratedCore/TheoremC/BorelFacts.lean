module

public import Mathlib.GroupTheory.Sylow
public import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.Models

public section

namespace CFSG.ProperTwoGeneratedCore.TheoremC

@[expose] def InCenterOf {K : Type*} [Group K] (Q : Subgroup K) (w : K) : Prop :=
  w ∈ Q ∧ ∀ q ∈ Q, Commute q w

structure BenderBorelFacts (K : Type*) [Group K] (Q : Subgroup K) : Prop where
  commutator_central : ∀ a ∈ Q, ∀ b ∈ Q, InCenterOf Q (a * b * a⁻¹ * b⁻¹)
  sq_central : ∀ a ∈ Q, InCenterOf Q (a * a)
  torus : ∃ D : Subgroup K, Odd (Nat.card D) ∧ D ≤ Subgroup.normalizer (Q : Set K) ∧
    Q ⊔ D = Subgroup.normalizer (Q : Set K) ∧
    (∀ w w' : K, InCenterOf Q w → w ≠ 1 → InCenterOf Q w' → w' ≠ 1 →
      ∃ d ∈ D, d⁻¹ * w * d = w') ∧
    (∀ β : K → K → ZMod 2,
      (∀ a ∈ Q, ∀ b ∈ Q, ∀ c ∈ Q, β (a * b) c = β a c + β b c) →
      (∀ a ∈ Q, ∀ b ∈ Q, ∀ c ∈ Q, β a (b * c) = β a b + β a c) →
      (∀ a ∈ Q, β a a = 0) →
      (∀ a ∈ Q, ∀ b : K, InCenterOf Q b → β a b = 0) →
      (∀ d ∈ D, ∀ a ∈ Q, ∀ b ∈ Q, β (d⁻¹ * a * d) (d⁻¹ * b * d) = β a b) →
      ∀ a ∈ Q, ∀ b ∈ Q, β a b = 0)
  center_card : 4 ≤ Nat.card {w : K // InCenterOf Q w}
  aut_inner : ∀ σ : MulAut K, (∀ q ∈ Q, σ q = q) → ∃ r ∈ Q, ∀ k : K, σ k = r * k * r⁻¹

@[expose] def PSL2BorelFacts : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∃ Q : Sylow 2 (CFSG.Theory.Comparator.PSL2Model n),
    BenderBorelFacts (CFSG.Theory.Comparator.PSL2Model n) (Q : Subgroup _)

@[expose] def SuzukiBorelFacts : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∃ Q : Sylow 2 ↥(CFSG.Theory.Comparator.SzModel n),
    BenderBorelFacts ↥(CFSG.Theory.Comparator.SzModel n) (Q : Subgroup _)

@[expose] def UnitaryBorelFacts : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∃ Q : Sylow 2 ↥(CFSG.Theory.Comparator.PSU3Model n),
    BenderBorelFacts ↥(CFSG.Theory.Comparator.PSU3Model n) (Q : Subgroup _)

@[expose] def BenderBorelFactsHold : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.BenderSuzuki.IsBenderGroup K →
    ∀ Q : Sylow 2 K, BenderBorelFacts K (Q : Subgroup K)

end CFSG.ProperTwoGeneratedCore.TheoremC
