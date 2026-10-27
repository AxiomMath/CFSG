module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.SylowRows
public import CFSG.Sporadic.FischerOddCore.Fi22ExtSylowCheckInputs

public section

namespace CFSG.EvenSporadicStandard.HypOne.Fi22

open CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Schreier.Native
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.FischerOddCore CFSG.Monster.B.Fischer

@[expose] def hypHex : String := include_str "Fi22Hyp.txt"

@[expose] def hypTbl (j : ℕ) : Table := hexT 3 3510 (3510 * j) hypHex

@[expose] def tT (k : ℕ) : Table := (fi22ExtArr (21 + k)).map UInt32.ofNat

@[expose] def uT : Table := fi22GraphOuterArr.map UInt32.ofNat

@[expose] def siftP (T : Table) : Bool := fi22InP (natArr T)

@[expose] def siftR (T : Table) : Bool := siftP T || siftP (compT 3510 T uT)

@[expose] def memP (t T : Table) : Bool := siftP T && commTT 3510 T t

@[expose] def memR (t T : Table) : Bool := siftR T && commTT 3510 T t

@[expose] def sgP : ℕ → Array Table
  | 0 => #[hypTbl 0, hypTbl 1, hypTbl 2]
  | 1 => #[hypTbl 6, hypTbl 7, hypTbl 8, hypTbl 9]
  | _ => #[hypTbl 13, hypTbl 14, hypTbl 15, hypTbl 16, hypTbl 17]

@[expose] def zT : ℕ → Table
  | 0 => hypTbl 3
  | 1 => hypTbl 10
  | _ => hypTbl 18

@[expose] def cgP : ℕ → Array Table
  | 0 => #[hypTbl 4, hypTbl 5]
  | 1 => #[hypTbl 11, hypTbl 12]
  | _ => #[hypTbl 19, hypTbl 20]

@[expose] def sgO : ℕ → Array Table
  | 3 => #[hypTbl 21, hypTbl 22, hypTbl 23, hypTbl 24, hypTbl 25]
  | 4 => #[hypTbl 28, hypTbl 29, hypTbl 30, hypTbl 31, hypTbl 32]
  | _ => #[hypTbl 35, hypTbl 36, hypTbl 37, hypTbl 38, hypTbl 39, hypTbl 40]

@[expose] def cgO : ℕ → Array Table
  | 3 => #[hypTbl 26, hypTbl 27]
  | 4 => #[hypTbl 33, hypTbl 34]
  | _ => #[hypTbl 41, hypTbl 42]

@[expose] def lT (k : ℕ) : Table := hypTbl (40 + k)

@[expose] def sylowP0 : Bool :=
  sylowFourOK 3510 65536 4 (memP (tT 0)) (cgP 0) (sgP 0) 65536

@[expose] def sylowP1 : Bool :=
  sylowFourOK 3510 131072 4 (memP (tT 1)) (cgP 1) (sgP 1) 131072

@[expose] def sylowP2 : Bool :=
  sylowFourOK 3510 65536 4 (memP (tT 2)) (cgP 2) (sgP 2) 65536

@[expose] def sylowR0 : Bool :=
  sylowFourOK 3510 131072 4 (memR (tT 0)) (cgP 0 ++ #[zT 0]) (sgP 0 ++ #[zT 0]) 131072

@[expose] def sylowR1 : Bool :=
  sylowFourOK 3510 262144 4 (memR (tT 1)) (cgP 1 ++ #[zT 1]) (sgP 1 ++ #[zT 1]) 262144

@[expose] def sylowR2 : Bool :=
  sylowFourOK 3510 131072 4 (memR (tT 2)) (cgP 2 ++ #[zT 2]) (sgP 2 ++ #[zT 2]) 131072

@[expose] def sylowR3 : Bool :=
  sylowFourOK 3510 16384 4 (memR (tT 3)) (cgO 3) (sgO 3) 16384

@[expose] def sylowR4 : Bool :=
  sylowFourOK 3510 16384 4 (memR (tT 4)) (cgO 4) (sgO 4) 16384

@[expose] def sylowR5 : Bool :=
  sylowFourOK 3510 2048 4 (memR (tT 5)) (cgO 5) (sgO 5) 2048

@[expose] def zData : Bool :=
  zOK 3510 siftP uT (tT 0) (zT 0) && zOK 3510 siftP uT (tT 1) (zT 1) &&
    zOK 3510 siftP uT (tT 2) (zT 2) && zOK 3510 siftP uT (tT 3) (tT 3) &&
    zOK 3510 siftP uT (tT 4) (tT 4) && zOK 3510 siftP uT (tT 5) (tT 5)

@[expose] def foursData : Bool :=
  foursWitOK 3510 siftP (lT 3) (tT 3) && foursWitOK 3510 siftP (lT 4) (tT 4) &&
    foursWitOK 3510 siftP (lT 5) (tT 5)

end CFSG.EvenSporadicStandard.HypOne.Fi22
