module

public import CFSG.HardMathSupport.Seitz.G2Noninner.Coordinator.Vacuous
public import CFSG.HardMathSupport.Seitz.Proving.SL2OrderThree

public section

namespace CFSG.HardMathSupport.Seitz.G2Noninner.Coordinator

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
  CFSG.RankThree.PartOne CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField

section Three

theorem seitzExcOuterNarrowG2Three_proved : SeitzExcOuterNarrowG2Three :=
  seitzExcOuterNarrowG2Three_of_SL2 Proving.exists_orderOf_three_SL2

end Three

end CFSG.HardMathSupport.Seitz.G2Noninner.Coordinator
