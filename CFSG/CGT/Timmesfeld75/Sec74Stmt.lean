module

public import CFSG.CGT.Timmesfeld75.Sec6Ctx

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open

@[expose] def Sec74 : Prop :=
  ∀ (G : Type) [Group G] (T T₁ : Subgroup G) (n m : ℕ), Sec6Ctx T T₁ n m →
    NaturalSL T (hSub T (normIn T₁ T)) n m → 3 ≤ n → ¬ (n = 4 ∧ m = 1) →
      ∀ a ∈ classD T, ∀ b ∈ classD T, orderOf (a * b) = 4 →
        (∃ h : G, a ∈ conjSubgroup h T ∧ b⁻¹ * a * b ∈ conjSubgroup h T) ∨
        (∃ g : G, b ∈ conjSubgroup g T ∧ a⁻¹ * b * a ∈ conjSubgroup g T)

end CFSG.CGT.Timmesfeld75
