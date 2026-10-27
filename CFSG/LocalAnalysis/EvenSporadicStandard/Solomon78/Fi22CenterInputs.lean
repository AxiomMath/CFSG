module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.SylowCenter
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.UMovWitness
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Fi22Inputs

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Schreier.Native
open CFSG.Sporadic.SmallOddCore CFSG.EvenSporadicStandard.HypOne.Fi22

@[expose] def centerP0 : Bool :=
  sylowCenterOK 3510 65536 (memP (tT 0)) (cgP 0) (sgP 0) 65536 (tT 0)

@[expose] def centerP1 : Bool :=
  sylowCenterOK 3510 131072 (memP (tT 1)) (cgP 1) (sgP 1) 131072 (tT 1)

@[expose] def centerP2 : Bool :=
  sylowCenterOK 3510 65536 (memP (tT 2)) (cgP 2) (sgP 2) 65536 (tT 2)

@[expose] def centerR3 : Bool :=
  sylowCenterOK 3510 16384 (memR (tT 3)) (cgO 3) (sgO 3) 16384 (tT 3)

@[expose] def centerR4 : Bool :=
  sylowCenterOK 3510 16384 (memR (tT 4)) (cgO 4) (sgO 4) 16384 (tT 4)

@[expose] def fi22UmovHex : String := include_str "Fi22UMoves.txt"

@[expose] def fi22UmovTbl (k : ℕ) : Table := hexT 3 3510 (3510 * k) fi22UmovHex

@[expose] def fi22UmovData : Bool :=
  (List.range 3).all fun i => (List.range 6).all fun j =>
    umovWitOK 3510 siftP (fi22UmovTbl (6 * i + j)) (tT i) (tT j)

end CFSG.EvenSporadicStandard.Solomon78
