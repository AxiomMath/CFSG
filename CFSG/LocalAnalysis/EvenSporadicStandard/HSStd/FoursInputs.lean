module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.SylowRows
public import CFSG.Sporadic.SmallOddCore.HSCheckInputs

public section

namespace CFSG.EvenSporadicStandard.HSStd

open CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Schreier.Native
open CFSG.Sporadic.SmallOddCore CFSG.EvenSporadicStandard.HypOne

abbrev rho0 : Table := hsCentTbl 5

abbrev rho1 : Table := hsCentTbl 12

abbrev rho2 : Table := hsCentTbl 21

abbrev rho3 : Table := hsCentTbl 34

@[expose] def foursHex : String := include_str "HSStd4G.txt"

@[expose] def foursTbl (k : ℕ) : Table := hexT 3 3850 (3850 * k) foursHex

@[expose] def foursData : Bool :=
  foursWitOK 3850 hsSift (foursTbl 0) rho2 && foursWitOK 3850 hsSift (foursTbl 1) rho3

end CFSG.EvenSporadicStandard.HSStd
