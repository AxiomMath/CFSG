module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.WCheck
public import CFSG.Sporadic.SmallOddCore.J3DataInputs

public section

namespace CFSG.EvenSporadicStandard.Fin76b.J3

open CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore

@[expose] def wGensJ3 : Array Table :=
  #[j3CentTbl 10, j3CentTbl 11, j3CentTbl 12, j3CentTbl 13, j3CentTbl 14]

end CFSG.EvenSporadicStandard.Fin76b.J3
