module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.FoursInputs

public section

namespace CFSG.EvenSporadicStandard.TwoHS

open CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Schreier.Native
open CFSG.Sporadic.SmallOddCore CFSG.EvenSporadicStandard.HypOne CFSG.EvenSporadicStandard.HSStd

@[expose] def coverHex : String := include_str "CoverConj.txt"

@[expose] def coverConjTbl (k : ℕ) : Table := hexT 3 3850 (3850 * k) coverHex

@[expose] def coverGen (l : ℤ) : Table := hsPGTbls[l.toNat]!

@[expose] def coverXHalf : List ℤ := [0, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1]

@[expose] def coverXWord : List ℤ := coverXHalf ++ coverXHalf

@[expose] def coverNWord : List ℤ := [0, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 0, 1, 1]

@[expose] def coverX : Table := wordT 3850 coverGen coverXWord

@[expose] def coverN : Table := wordT 3850 coverGen coverNWord

@[expose] def coverNInv : Table := invT 3850 coverN

@[expose] def coverX2 : Table := conjT 3850 coverN coverNInv coverX

@[expose] def coverX3 : Table := conjT 3850 coverN coverNInv coverX2

@[expose] def coverNInvOK : Bool := invOK 3850 coverN coverNInv

@[expose] def coverXNeOK : Bool := !tblEq 3850 coverX (idT 3850)

@[expose] def coverXSqOK : Bool := tblEq 3850 (compT 3850 coverX coverX) (idT 3850)

@[expose] def coverComm2OK : Bool := commTT 3850 coverX coverX2

@[expose] def coverComm3OK : Bool := commTT 3850 coverX coverX3

@[expose] def coverConj3OK : Bool :=
  tblEq 3850 (conjT 3850 coverN coverNInv coverX3) (compT 3850 coverX coverX2)

@[expose] def coverPermOK (T : Table) : Bool := permOK 3850 T && invOK 3850 T (invT 3850 T)

@[expose] def coverMemOK (T : Table) : Bool := coverPermOK T && hsSift T

@[expose] def coverConjEqOK (l c ρ : Table) : Bool :=
  tblEq 3850 (commTable 3850 l ρ) (conjT 3850 c (invT 3850 c) coverX)

end CFSG.EvenSporadicStandard.TwoHS
