module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5BCMultiModel
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5BCMultiAltFour
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5BCMultiAltThree

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS
open scoped commutatorElement

section Model

variable {n : ℕ} {K : Type} [Group K] [Finite K]

theorem exists_sl23_model (C : AhatData.CoverSetup n K) (hn : 8 ≤ n) {α : MulAut K}
    {σ : Perm (Fin n)} (hα : C.Induces α σ) (hσ : σ * σ = 1)
    (hbad : fixCount σ = 4 ∨ (transCount σ = 3 ∧ fixCount σ ≤ 3)) :
    ∃ P Qb : Subgroup K, P ≤ AhatData.fixSub α ∧
      (∀ g ∈ AhatData.fixSub α, ∀ p ∈ P, g * p * g⁻¹ ∈ P) ∧ Nonempty (↥P ≃* SL23) ∧
      (∀ N : Subgroup K, N ≤ P → (∀ p ∈ P, ∀ x ∈ N, p * x * p⁻¹ ∈ N) → Odd (Nat.card ↥N) →
        N = ⊥) ∧
      Qb ≤ P ∧ Nat.card ↥Qb = 8 ∧ (∀ g ∈ AhatData.fixSub α, ∀ q ∈ Qb, g * q * g⁻¹ ∈ Qb) ∧
      (∀ q ∈ Qb, q ≠ 1 → ∃ k : ℕ, q ^ k ∈ center K ∧ q ^ k ≠ 1) ∧
      ∃ a ∈ Qb, ∃ b ∈ Qb, ⁅a, b⁆ ∈ center K ∧ ⁅a, b⁆ ≠ 1 := by
  rcases hbad with h4 | ⟨h3, -⟩
  · obtain ⟨W₀, h1, h2, h3, h4', h5⟩ := exists_alt4_fixed (n := n) (σ := σ) h4
    exact exists_sl23_model_of_alt4 C hn hα h1 h2 h3 h4' h5
  · obtain ⟨W₀, h1, h2, h3', h4', h5⟩ := exists_alt4_three hσ h3
    exact exists_sl23_model_of_alt4 C hn hα h1 h2 h3' h4' h5

end Model

end CFSG.OddStandard.Solomon75
