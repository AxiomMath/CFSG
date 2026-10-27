module

public import CFSG.CGT.Timmesfeld75.Sec6Ctx

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open

@[expose] def Sec78 : Prop :=
  ∀ (G : Type) [Group G] (T T₁ : Subgroup G) (n m : ℕ), Sec6Ctx T T₁ n m →
    NaturalSL T (hSub T (normIn T₁ T)) n m → 4 ≤ n → ¬ (n = 4 ∧ m = 1) →
      ∀ d ∈ classD T, ∀ e ∈ classD T, ∀ k : ℕ, Odd k → 3 ≤ k → orderOf (d * e) ≠ 2 * k

@[expose] def Sec710 : Prop :=
  ∀ (G : Type) [Group G] (T T₁ : Subgroup G) (m : ℕ), Sec6Ctx T T₁ 3 m →
    NaturalSL T (hSub T (normIn T₁ T)) 3 m → 2 ≤ m →
      ∀ d ∈ classD T, ∀ e ∈ classD T, ∀ k : ℕ, Odd k → 3 ≤ k → orderOf (d * e) ≠ 2 * k

end CFSG.CGT.Timmesfeld75
