module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RYCheck
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.BetaCheck

public section

namespace CFSG.EvenSporadicStandard.Fin76b.S16

open CFSG.Sporadic.SmallOddCore CFSG.EvenSporadicStandard.Fin76b.Beta

@[expose] def j2S16OK : Bool :=
  s16Check 315 40 j2Sift (j2CentTbl 0) (j2CentTbl 31) (j2BetaTbl 7) (j2Tb 0) (j2Tb 1) (j2Tb 2)
    [j2Tb 3, j2Tb 4, j2Tb 5, j2Tb 6] [j2Tb 7, j2Tb 8, j2Tb 9, j2Tb 10, j2Tb 11]
    [true, false, false, false, false]

@[expose] def j3S16OK : Bool :=
  s16Check 6156 40 j3Sift (j3CentTbl 0) (j3CentTbl 9) (j3BetaTbl 7) (j3Tb 0) (j3Tb 1) (j3Tb 2)
    [j3Tb 3, j3Tb 4, j3Tb 5, j3Tb 6] [j3Tb 7, j3Tb 8, j3Tb 9, j3Tb 10]
    [true, false, false, true]

end CFSG.EvenSporadicStandard.Fin76b.S16
