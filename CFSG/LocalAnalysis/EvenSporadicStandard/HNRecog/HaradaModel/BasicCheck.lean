module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.WordData

public section

namespace CFSG.EvenSporadicStandard.HNRecog.HaradaModel

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore
  CFSG.Sporadic.SmallOddCore.Native

@[expose] def gensInvoOK : Bool := (List.range 7).all fun j => invoOK 1408 (tabW [j + 1])

end CFSG.EvenSporadicStandard.HNRecog.HaradaModel
