module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3XData
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaN2Data

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaSec3

open CFSG.Fischer CFSG.F4.Native CFSG.Certificates CFSG.Certificates.Native
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native
open CFSG.EvenSmallLie.UnitarySix.YamadaPar CFSG.EvenSmallLie.UnitarySix.YamadaN2

@[expose] def y14Basis : List ℕ := [14, 12, 13, 9, 10, 11, 4, 7, 8]

@[expose] def y14V : List (List ℕ) :=
  [[0], [1], [5], [6], [15, 0, 15], [15, 1, 15], [2], [3], [15, 16, 2, 16, 15],
    [15, 16, 3, 16, 15], [16, 2, 16], [16, 3, 16]]

@[expose] def iotaWordOf (m : ℕ) : List ℕ :=
  (List.range 9).flatMap fun i => if m.testBit i then [y14Basis[i]!] else []

@[expose] def colBits (s : Fin 12) (i : ℕ) : ℕ :=
  bitsOf 9 fun r => ((genABits s).getD r 0).testBit i

@[expose] def y14Check : Bool :=
  (List.finRange 12).all fun s => (List.range 9).all fun i =>
    eqA 693 (wA (cjW y14V[s.val]! [y14Basis[i]!])) (wA (iotaWordOf (colBits s i)))

end CFSG.EvenSmallLie.UnitarySix.YamadaSec3
