module

public import CFSG.CGT.Timmesfeld75.Sec6Ctx

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open

@[expose] def Sec77 : Prop :=
  ∀ (G : Type) [Group G] (T T₁ : Subgroup G) (n m : ℕ), Sec6Ctx T T₁ n m →
    NaturalSL T (hSub T (normIn T₁ T)) n m → 3 ≤ n → ¬ (n = 4 ∧ m = 1) →
      ∀ x ∈ classD T, ∀ z ∈ classD T, x * z = z * x → x * z ≠ 1 → x * z ∉ classD T →
        ∀ y ∈ classD T, y * (x * z) = (x * z) * y → orderOf (x * y) ≠ 4

end CFSG.CGT.Timmesfeld75
