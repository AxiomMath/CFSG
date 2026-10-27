module

public import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6KD

theorem even_card_of_nonabelian_simple (J : Type) [Group J] [Finite J] [IsSimpleGroup J]
    (hnab : ¬ ∀ a b : J, a * b = b * a) : Even (Nat.card J) := by
  by_contra hodd
  have hodd' : Odd (Nat.card J) := Nat.not_even_iff_odd.mp hodd
  exact hnab (IsSimpleGroup.comm_iff_isSolvable.mpr (CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd'))

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6KD
