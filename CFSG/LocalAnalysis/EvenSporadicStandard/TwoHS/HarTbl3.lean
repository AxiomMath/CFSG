module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.HarTbl

public section

namespace CFSG.EvenSporadicStandard.TwoHS

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore

@[expose] def harWInvOK : Bool :=
  tblEq 11200 (compT 11200 (tU [1]) (tU [1])) (idT 11200) && !tblEq 11200 (tU [1]) (idT 11200) &&
  tblEq 11200 (compT 11200 (tU [2, 3, 3]) (tU [2, 3, 3])) (idT 11200) &&
  !tblEq 11200 (tU [2, 3, 3]) (idT 11200)

end CFSG.EvenSporadicStandard.TwoHS
