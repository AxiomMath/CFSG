module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.SylowRows
public import CFSG.Sporadic.SmallOddCore.J3CheckInputs

public section

namespace CFSG.EvenSporadicStandard.HypOne.J3

open CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Schreier.Native
open CFSG.Sporadic.SmallOddCore

@[expose] def hypHex : String := include_str "J3Hyp.txt"

@[expose] def hypTbl (k : ℕ) : Table := hexT 4 6156 (6156 * k) hypHex

abbrev t0 : Table := j3CentTbl 9

abbrev t1 : Table := j3CentTbl 21

@[expose] def z0 : Table := hypTbl 0

@[expose] def sgP0 : Array Table := #[hypTbl 1, hypTbl 2, hypTbl 3]

@[expose] def sgR1 : Array Table := #[hypTbl 4, hypTbl 5, hypTbl 6, hypTbl 7]

@[expose] def cgP0 : Array Table :=
  #[j3CentTbl 10, j3CentTbl 11, j3CentTbl 12, j3CentTbl 13, j3CentTbl 14]

@[expose] def cgR0 : Array Table :=
  #[j3CentTbl 10, j3CentTbl 11, j3CentTbl 12, j3CentTbl 13, j3CentTbl 14, z0]

@[expose] def cgR1 : Array Table := #[j3CentTbl 22, j3CentTbl 23, j3CentTbl 24, t1]

@[expose] def memP (t T : Table) : Bool := j3Sift T && commTT 6156 T t

@[expose] def memR (t T : Table) : Bool :=
  (j3Sift T || j3Sift (compT 6156 T j3OuterTbl)) && commTT 6156 T t

@[expose] def sylowData : Bool :=
  permOK 6156 j3OuterTbl && permOK 6156 t0 && permOK 6156 t1 &&
    sylowFourOK 6156 128 6 (memP t0) cgP0 sgP0 128 &&
    sylowFourOK 6156 256 6 (memR t0) cgR0 j3SylowGenTbls.toArray 256 &&
    sylowFourOK 6156 32 6 (memR t1) cgR1 sgR1 32 &&
    zOK 6156 j3Sift j3OuterTbl t0 z0 && zOK 6156 j3Sift j3OuterTbl t1 t1

@[expose] def e8Data : Bool := e8Rows 6156 j3Sift (hypTbl 8) (hypTbl 9) (hypTbl 10)

@[expose] def foursData : Bool := foursWitOK 6156 j3Sift (hypTbl 11) t1

end CFSG.EvenSporadicStandard.HypOne.J3
