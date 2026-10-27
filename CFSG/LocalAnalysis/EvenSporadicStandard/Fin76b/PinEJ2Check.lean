module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.PinE
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverModelsNative

public section

namespace CFSG.EvenSporadicStandard.Fin76b.J2

open CFSG.ComponentClassification.J2Cover.Models

@[expose] def mulJ2 (a b : ℕ) : ℕ := (mulTab[a]!)[b]!

@[expose] def j2PinCheck : Bool := TablePin.pinCheck 128 mulJ2 4

end CFSG.EvenSporadicStandard.Fin76b.J2
