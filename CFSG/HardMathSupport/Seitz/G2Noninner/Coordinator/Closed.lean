module

public import CFSG.HardMathSupport.Seitz.G2Noninner.Descent.OddPower
public import CFSG.HardMathSupport.Seitz.G2Noninner.SubfieldPair.Final

public section

namespace CFSG.HardMathSupport.Seitz.G2Noninner.Coordinator

open CFSG.LieType.SeitzGeneration CFSG.RankThree.PartOne

theorem seitzExcOuterNarrowG2OddPower_proved : SeitzExcOuterNarrowG2OddPower :=
  seitzExcOuterNarrowG2OddPower_of_pair subfieldPairG2Odd

end CFSG.HardMathSupport.Seitz.G2Noninner.Coordinator
