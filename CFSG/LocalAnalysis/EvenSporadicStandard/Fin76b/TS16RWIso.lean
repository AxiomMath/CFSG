module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.UTableSpec
public import CFSG.Sporadic.SmallOddCore.GroupFacts
public import Certificates.Data.CFSGNative.SmallOddCore.Check

public section

namespace CFSG.EvenSporadicStandard.Fin76b.W16

open CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
  CFSG.Sporadic.Schreier.Native

@[expose] def rhoInvArr : Array Nat :=
  #[0, 1, 2, 3, 14, 4, 7, 5, 12, 17, 18, 9, 20, 8, 11, 6, 10, 13, 19, 15, 16, 21, 23, 27, 25, 22,
    24, 26, 28, 29, 31, 30]

end CFSG.EvenSporadicStandard.Fin76b.W16
