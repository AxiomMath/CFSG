module

public import CFSG.CGT.Timmesfeld75.PaperSteps

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped commutatorElement

@[expose] def Sec68CorB : Prop :=
  ∀ (G : Type) [Group G] (T T₁ : Subgroup G) (m : ℕ), StepHyp T T₁ → 2 ≤ m →
    Nat.card T / Nat.card ↥(normIn T T₁) = 2 ^ m → Nat.card T = (2 ^ m) ^ 2 →
    NaturalSL T (hSub T (normIn T₁ T)) 2 m →
    (∀ d ∈ classD T, ∀ e ∈ classD T, d ≠ e → d * e = e * d → d * e ∈ classD T) →
    (∀ d ∈ normIn T T₁, d ≠ 1 →
      Subgroup.closure {e : G | e ∈ classD T ∧ e * d = d * e} = T ⊔ normIn T₁ T) →
    (∀ z ∈ T ⊔ normIn T₁ T,
      ((∀ w ∈ T ⊔ normIn T₁ T, z * w = w * z) ↔ z ∈ normIn T T₁)) →
    (∀ a ∈ T ⊔ normIn T₁ T, ∀ b ∈ T ⊔ normIn T₁ T, ⁅a, b⁆ ∈ normIn T T₁) →
    (∀ N : Subgroup G, N ≤ hSub T (normIn T₁ T) →
      (∀ h ∈ hSub T (normIn T₁ T), conjSubgroup h N = N) → IsPGroup 2 N → N ≤ T) →
    ListGroup G

end CFSG.CGT.Timmesfeld75
