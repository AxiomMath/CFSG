module

public import CFSG.CGT.Timmesfeld75.Sec25

public section

namespace CFSG.CGT.T75I

open CFSG.CGT.Timmesfeld75

@[expose] def AschbacherDisconnectedInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (D : Set G),
    (∃ d₀ : G, D = {g | IsConj d₀ g}) → (∀ d ∈ D, orderOf d = 2) →
    Subgroup.closure D = ⊤ →
    (∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) →
    (∃ x ∈ D, ∃ y ∈ D, ¬ ReachD D x y) →
    (∀ x ∈ D, ∀ y ∈ D, x * y = y * x → x ≠ y → x * y ∈ D) →
    (∃ u ∈ D, ∃ v ∈ D, u ≠ v ∧ u * v = v * u) →
    CFSG.BenderSuzuki.IsBenderGroup G

end CFSG.CGT.T75I
