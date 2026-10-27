module

public import CFSG.LocalAnalysis.OddStandard.AltStdCycTwoBigMain
public import CFSG.LocalAnalysis.OddStandard.AltStdCycTwoBigFull

public section

namespace CFSG.OddStandard.AltStdCycTwo

open Subgroup

theorem cycTwoBigFalse_holds : CycTwoBigFalse :=
  cycTwoBigFalse_of_fullPair cycTwoBigFullPairFalse_holds

end CFSG.OddStandard.AltStdCycTwo
