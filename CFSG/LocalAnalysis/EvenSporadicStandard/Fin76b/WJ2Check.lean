module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.WCheck
public import CFSG.Sporadic.SmallOddCore.J2DataInputs

public section

namespace CFSG.EvenSporadicStandard.Fin76b.J2

open CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore

@[expose] def wGensJ2 : Array Table :=
  #[j2CentTbl 32, j2CentTbl 33, j2CentTbl 34, j2CentTbl 35]

end CFSG.EvenSporadicStandard.Fin76b.J2
