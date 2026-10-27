module

public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderTriality

public section

namespace CFSG.HardMathSupport.Lang.Coordinator

open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)
open CFSG.ComponentClassification.CatLeaf (lieOrderNumerator)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

@[expose] def OuterFixedOrderTrialityThreeChar (P : ℕ → Prop) : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (n ℓ f : ℕ), P ℓ →
    StatedLieAdmissible .trialityD4 n ℓ f → CFSG.Blueprint.LieModel K .trialityD4 n ℓ f →
    ∀ α : MulAut K, α ^ 3 = 1 → α ∉ inner K →
      (∃ f₀ : ℕ, f = 3 * f₀ ∧
        Nat.card (fixedSubgroup α) ∣ lieOrderNumerator .trialityD4 n (ℓ ^ f₀)) ∨
      Nat.card (fixedSubgroup α) ∣ lieOrderNumerator .G2 0 (ℓ ^ f)

theorem outerFixedOrderTrialityThree_of_chars
    (h2 : OuterFixedOrderTrialityThreeChar (· = 2)) (h3 : OuterFixedOrderTrialityThreeChar (· = 3))
    (h5 : OuterFixedOrderTrialityThreeChar (5 ≤ ·)) : OuterFixedOrderTrialityThree := by
  intro K _ _ n ℓ f hadm hmodel α hα3 hαin
  have hℓ : ℓ.Prime := hadm.1
  have hcases : ℓ = 2 ∨ ℓ = 3 ∨ 5 ≤ ℓ := by
    have h2ℓ := hℓ.two_le
    by_contra hcon
    push Not at hcon
    have h4 : ℓ = 4 := by omega
    subst h4
    exact absurd hℓ (by norm_num)
  rcases hcases with h | h | h
  · exact h2 K n ℓ f h hadm hmodel α hα3 hαin
  · exact h3 K n ℓ f h hadm hmodel α hα3 hαin
  · exact h5 K n ℓ f h hadm hmodel α hα3 hαin

end CFSG.HardMathSupport.Lang.Coordinator
