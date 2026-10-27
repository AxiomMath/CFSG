module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.SylowCenter
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.UMovWitness
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.SuzInputs

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Schreier.Native
open CFSG.Sporadic.SmallOddCore CFSG.EvenSporadicStandard.HypOne.Suz

@[expose] def centerM0 : Bool :=
  sylowCenterOK 1782 512 (memM (tT 0)) #[hypTbl 4, hypTbl 5]
    #[hypTbl 0, hypTbl 1, hypTbl 2, hypTbl 3] 512 (tT 0)

@[expose] def centerM1 : Bool :=
  sylowCenterOK 1782 8192 (memM (tT 1)) #[hypTbl 10, hypTbl 11]
    #[hypTbl 6, hypTbl 7, hypTbl 8, hypTbl 9] 8192 (tT 1)

@[expose] def umovHex : String := include_str "SuzUMoves.txt"

@[expose] def umovTbl (k : ℕ) : Table := hexT 3 1782 (1782 * k) umovHex

@[expose] def umovData : Bool :=
  (List.range 2).all fun i => (List.range 4).all fun j =>
    umovWitOK 1782 siftM (umovTbl (4 * i + j)) (tT i) (tT j)

end CFSG.EvenSporadicStandard.Solomon78
