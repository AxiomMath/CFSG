module

public import CFSG.Sporadic.Co1.Cover.Data

public section

namespace CFSG.EvenSporadicStandard.TwoCo1

open CFSG.Sporadic.Co1.Cover CFSG.Sporadic.Co1.CoverNative

@[expose] def eMaskA : ℕ := 3

@[expose] def eMaskC : ℕ := 1

@[expose] def eRowsA : Array ℕ := eprodRows epsRows eMaskA

@[expose] def eRowsC : Array ℕ := eprodRows epsRows eMaskC

end CFSG.EvenSporadicStandard.TwoCo1
