module

public import CFSG.CGT.Timmesfeld75.Sec4CaseIPartition

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open

@[expose] def Sec4I4TrivialAction : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    SimpleCaseUpTo (Nat.card G) →
    ∀ (T T₁ T₂ : Subgroup G) (a : G), Sec4Hyp T T₁ a T₂ →
    2 * Nat.card (normIn T T₁) < Nat.card T → Nat.card T ≠ 16 →
      ∀ x : G, x ∈ classD T → x ∈ Subgroup.normalizer (T : Set G) →
        Sec4ActsTriv T T₁ T₂ x → x ∈ sec4N T T₁ T₂

@[expose] def Sec4I4OuterAction : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    SimpleCaseUpTo (Nat.card G) →
    ∀ (T T₁ T₂ : Subgroup G) (a : G), Sec4Hyp T T₁ a T₂ →
    2 * Nat.card (normIn T T₁) < Nat.card T → Nat.card T ≠ 16 →
      ∀ x : G, x ∈ classD T → x ∈ Subgroup.normalizer (T : Set G) →
        x ∈ Subgroup.normalizer (sec4N T T₁ T₂ : Set G) →
          (∀ t ∈ T, ¬ Sec4ActsTriv T T₁ T₂ (x * t)) → False

end CFSG.CGT.Timmesfeld75
