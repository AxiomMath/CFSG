module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.SylowRows
public import CFSG.Sporadic.SuzOddCore.InvTCheckInputs

public section

namespace CFSG.EvenSporadicStandard.HypOne.Suz

open CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Schreier.Native
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SuzOddCore

@[expose] def hypHex : String := include_str "SuzHyp.txt"

@[expose] def hypTbl (k : ℕ) : Table := hexT 3 1782 (1782 * k) hypHex

@[expose] def tT (i : ℕ) : Table := (tArr i).map UInt32.ofNat

@[expose] def vT : Table := vArr.map UInt32.ofNat

@[expose] def siftM (T : Table) : Bool := inM (natArr T)

@[expose] def memM (t T : Table) : Bool := siftM T && commTT 1782 T t

@[expose] def memT (t T : Table) : Bool :=
  (siftM T || siftM (compT 1782 vT T)) && commTT 1782 T t

@[expose] def sylowM0 : Bool :=
  sylowFourOK 1782 512 6 (memM (tT 0)) #[hypTbl 4, hypTbl 5]
    #[hypTbl 0, hypTbl 1, hypTbl 2, hypTbl 3] 512

@[expose] def sylowM1 : Bool :=
  sylowFourOK 1782 8192 6 (memM (tT 1)) #[hypTbl 10, hypTbl 11]
    #[hypTbl 6, hypTbl 7, hypTbl 8, hypTbl 9] 8192

@[expose] def sylowT0 : Bool :=
  sylowFourOK 1782 1024 6 (memT (tT 0))
    #[hypTbl 18, hypTbl 19, hypTbl 20, hypTbl 21, hypTbl 22]
    #[hypTbl 12, hypTbl 13, hypTbl 14, hypTbl 15, hypTbl 16, hypTbl 17] 1024

@[expose] def sylowT1 : Bool :=
  sylowFourOK 1782 16384 6 (memT (tT 1)) #[hypTbl 27, hypTbl 28]
    #[hypTbl 23, hypTbl 24, hypTbl 25, hypTbl 26] 16384

@[expose] def sylowT2 : Bool :=
  sylowFourOK 1782 256 6 (memT (tT 2)) #[hypTbl 33, hypTbl 34]
    #[hypTbl 29, hypTbl 30, hypTbl 31, hypTbl 32] 256

@[expose] def sylowT3 : Bool :=
  sylowFourOK 1782 512 6 (memT (tT 3)) #[hypTbl 39, hypTbl 40]
    #[hypTbl 35, hypTbl 36, hypTbl 37, hypTbl 38] 512

@[expose] def e8Data : Bool := e8Rows 1782 siftM (hypTbl 41) (hypTbl 42) (hypTbl 43)

@[expose] def foursData : Bool :=
  foursWitOK 1782 siftM (hypTbl 44) (tT 2) && foursWitOK 1782 siftM (hypTbl 45) (tT 3)

end CFSG.EvenSporadicStandard.HypOne.Suz
