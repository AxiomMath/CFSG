module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.PinE
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.J3Table

public section

namespace CFSG.EvenSporadicStandard.Fin76b.J3

@[expose] def j3PinCheck : Bool := TablePin.pinCheck 128 mulJ3 tIdxJ3

end CFSG.EvenSporadicStandard.Fin76b.J3
