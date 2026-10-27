module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CSixThreeOneDefs
import CFSG.LocalAnalysis.RankThreeUC.AGL81CSixThreeOneBasis
import CFSG.LocalAnalysis.RankThreeUC.AGL81CSixThreeOneDickson
import CFSG.LocalAnalysis.RankThreeUC.AGL81CSixThreeOneReducible
import CFSG.LocalAnalysis.RankThreeUC.AGL81CSixThreeOneIrredFive

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C.S631

open CFSG.RepresentationTheory

section


theorem matrixListAt_three_of_five_le {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) :
    MatrixListAt p 3 := by
  intro H hH
  by_cases hirr : IsIrreducibleMatrixRep H.subtype
  · rcases sl3_or_psl2_of_irreducible hp5 hH hirr with h | h
    · exact Or.inl (Or.inr (Or.inl h))
    · exact Or.inl (Or.inr (Or.inr (Or.inl h)))
  · rcases sl2_or_trivial_of_not_irreducible (sLTwoOrTrivialAt p) hH hirr with h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr (Or.inr (Or.inr h)))

theorem linearListAt_of_five_le {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) : LinearListAt p := by
  refine linearListAt_of_matrixListAt fun n hn => ?_
  rcases Nat.lt_or_ge n 3 with h | h
  · exact matrixListAt_of_le_two (by omega)
  · obtain rfl : n = 3 := le_antisymm hn h
    exact matrixListAt_three_of_five_le hp5

end

end CFSG.LocalAnalysis.RankThreeUC.AGL81C.S631
