module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.GlobBalance

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.Solomon78

@[expose] def Sol78Thm54Types (X : Type) [Group X] : Prop :=
  (∃ n : ℕ, 1 ≤ n ∧ SuzukiModel X 2 (2 * n + 1)) ∨
    ∃ m : ℕ, 3 ≤ m ∧ (LieModel X .PSp 2 2 m ∨ LieModel X .PSU 4 2 m ∨ LieModel X .PSL 4 2 m ∨
      LieModel X .PSU 5 2 m ∨ LieModel X .PSL 5 2 m)

end CFSG.EvenSporadicStandard.Induction
