module

public import CFSG.LieType.Universal.Symplectic

public section

namespace CFSG.ClassicalInvolution.Q3.Q3T6

open CFSG.Assembly.LowTwoRank

variable {K : Type} [Field K]

theorem isQuasisimple_sp_of_three_le (h : 3 ≤ Nat.card K) {m : ℕ} (hm : 2 ≤ m) :
    CFSG.IsQuasisimple (StatedSp m K) := by
  refine CFSG.LieType.Universal.Symplectic.isQuasisimple m K (by omega) ?_
  rcases (by omega : Nat.card K = 3 ∨ 4 ≤ Nat.card K) with h3 | h4
  · exact Or.inr (Or.inl ⟨h3, hm⟩)
  · exact Or.inl (Or.inr h4)

theorem isQuasisimple_sp4_of_three_le (h : 3 ≤ Nat.card K) : CFSG.IsQuasisimple (StatedSp 2 K) :=
  isQuasisimple_sp_of_three_le h le_rfl

theorem isPerfect_sp4_of_three_le (h : 3 ≤ Nat.card K) : Group.IsPerfect (StatedSp 2 K) :=
  (isQuasisimple_sp4_of_three_le h).1

end CFSG.ClassicalInvolution.Q3.Q3T6
