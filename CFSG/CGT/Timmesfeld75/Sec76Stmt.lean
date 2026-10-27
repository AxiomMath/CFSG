module

public import CFSG.CGT.Timmesfeld75.Sec6Ctx

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open

@[expose] def Sec76 : Prop :=
  ∀ (G : Type) [Group G] (T T₁ : Subgroup G) (n m : ℕ), Sec6Ctx T T₁ n m →
    NaturalSL T (hSub T (normIn T₁ T)) n m → 3 ≤ n → ¬ (n = 4 ∧ m = 1) →
      ∀ x ∈ classD T, ∀ y ∈ classD T, ∀ k : ℕ, Odd k → 3 ≤ k → orderOf (x * y) = 2 * k →
        ∀ a ∈ classD T, a * x = x * a → orderOf (a * y) ≠ 2 ∧ orderOf (a * y) ≠ 4

end CFSG.CGT.Timmesfeld75
