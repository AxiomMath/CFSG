module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CSixThreeOneDefs
import CFSG.LocalAnalysis.RankThreeUC.AGL81CSixThreeOneReduce
import CFSG.LocalAnalysis.RankThreeUC.AGL81CSixThreeOneBasis
import CFSG.LocalAnalysis.RankThreeUC.AGL81CSixThreeOneDickson
import CFSG.LocalAnalysis.RankThreeUC.AGL81CSixThreeOneReducible
import CFSG.LocalAnalysis.RankThreeUC.AGL81CSixThreeOneIrredThree
import CFSG.LocalAnalysis.RankThreeUC.AGL81CSixThreeOneSympThree
public import CFSG.RepresentationTheory.UniqueVectorOrbitTwisting

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C.S631

open CFSG.RepresentationTheory


theorem matrixListAt_three_three : MatrixListAt 3 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro H hH
  by_cases hirr : IsIrreducibleMatrixRep H.subtype
  · rcases sl3_or_psl2_or_frobenius_of_irreducible_three hH hirr with h | h | h
    · exact Or.inl (Or.inr (Or.inl h))
    · exact Or.inl (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr ⟨rfl, Or.inr (Or.inr (Or.inl h))⟩))
  · rcases sl2_or_trivial_of_not_irreducible (sLTwoOrTrivialAt 3) hH hirr with h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr (Or.inr (Or.inr h)))

theorem linearListAt_three : LinearListAt 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine linearListAt_of_matrixListAt fun n hn => ?_
  rcases Nat.lt_or_ge n 3 with h | h
  · exact matrixListAt_of_le_two (by omega)
  · obtain rfl : n = 3 := le_antisymm hn h
    exact matrixListAt_three_three

theorem sixThreeOneAt_three : SixThreeOneAt 3 :=
  sixThreeOneAt_of_lists Nat.prime_three (by decide) linearListAt_three sympListAt_three

end CFSG.LocalAnalysis.RankThreeUC.AGL81C.S631
