module

public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Algebra.Group.Subgroup.Defs

public section

namespace CFSG.EvenSporadicStandard.Fin76b

structure EFacts615 {G : Type*} [Group G] (E : Subgroup G) (t : G) : Prop where
  ea_le : ∀ A : Subgroup (MulAut ↥E), (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) →
    (∀ a ∈ A, a * a = 1) → Nat.card ↥A ≤ 16

end CFSG.EvenSporadicStandard.Fin76b
