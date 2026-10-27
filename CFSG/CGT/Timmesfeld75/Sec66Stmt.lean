module

public import CFSG.CGT.Timmesfeld75.Sec6Ctx

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open

@[expose] def Sec66 : Prop :=
  ∀ (G : Type) [Group G] (T T₁ : Subgroup G) (n m : ℕ), Sec6Ctx T T₁ n m →
    ∀ x ∈ classD T, ∀ y ∈ classD T, orderOf (x * y) = 4 → (x * y) ^ 2 ∈ classD T

end CFSG.CGT.Timmesfeld75
