module

public import CFSG.Blueprint.Catalog

public section

namespace CFSG.EvenSporadicStandard.Induction

open CFSG.Blueprint CFSG.Blueprint.NativeSporadic

structure Thm46Orders : Prop where
  psl3_gt : ∀ (X : Type) [Group X] (n : ℕ), 3 ≤ n → LieModel X .PSL 3 2 n → 95040 < Nat.card X
  g2_gt : ∀ (X : Type) [Group X] (n : ℕ), 2 ≤ n → LieModel X .G2 0 2 n → 95040 < Nat.card X
  suz_gt : ∀ (X : Type) [Group X], IsSporadic X .Suz → 95040 < Nat.card X
  psl3_not_sporadic : ∀ (X : Type) [Group X] [IsSimpleGroup X] (n : ℕ), 3 ≤ n →
    LieModel X .PSL 3 2 n → ¬ SporadicRep X
  g2_not_sporadic : ∀ (X : Type) [Group X] [IsSimpleGroup X] (n : ℕ), 2 ≤ n →
    LieModel X .G2 0 2 n → ¬ SporadicRep X
  psl3_ne_he : ∀ (X : Type) [Group X] (n : ℕ), 3 ≤ n → LieModel X .PSL 3 2 n →
    Nat.card X ≠ 4030387200
  g2_ne_he : ∀ (X : Type) [Group X] (n : ℕ), 2 ≤ n → LieModel X .G2 0 2 n →
    Nat.card X ≠ 4030387200

end CFSG.EvenSporadicStandard.Induction
