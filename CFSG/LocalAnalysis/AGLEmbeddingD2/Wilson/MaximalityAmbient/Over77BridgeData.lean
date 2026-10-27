module

public import CFSG.Sporadic.Schreier.J4SElevenData
public import Certificates.Data.J4M2.Orbit
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.MaximalityAmbient.Over77Data

public section

namespace CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.Over77

open CFSG.Sporadic.J4Schreier CFSG.Sporadic.GLQ CFSG.SectionRank.Native
open CFSG.Sporadic.J4.Native CFSG.Quasithin.J4M2

@[expose] def zRowsN : Array Nat := zM.map V2.toNat

@[expose] def zPN : Pair := (zRowsN, zRowsN)

@[expose] def hWordN : List ℤ :=
  [1, 2, -2, -2, -1, 2, -2, -1, -2, -1, -2, 2, 2, 1, 2, 2, 2, 2, 1, -2]

@[expose] def hWP : Pair := wordP An Bn hWordN

@[expose] def jInvP : Pair := powP H2n 20

@[expose] def gamP : Pair :=
  mulP (powP (mulP zPN (mulP (mulP hWP jInvP) (invP hWP))) 6) hWP

@[expose] def c1jP : Pair := mulP (powP QYn 10) H1n

@[expose] def cAP : Pair := mulP (mulP gamP c1jP) (invP gamP)

@[expose] def cBP : Pair := mulP (mulP gamP H2n) (invP gamP)

@[expose] def cZP : Pair := mulP (mulP gamP QZn) (invP gamP)

@[expose] def actOK (X π : Array Nat) : Bool :=
  (List.range 77).all fun i =>
    decide (π.getD i 0 < 77) &&
      decide (frApply (frTable (X.map natToV2)) vecs[π.getD i 0]! = vecs[i]!)

@[expose] def commOK (X : Array Nat) : Bool := O.eq (O.mul X zRowsN) (O.mul zRowsN X)

@[expose] def bridgeCheck : Bool :=
  zM.size == 112 && O.eq (O.mul zRowsN zRowsN) O.one &&
    actOK cAP.1 dataA && actOK cBP.1 dataB && actOK cZP.1 dataZ &&
    commOK cAP.1 && commOK cBP.1 && commOK cZP.1

end CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.Over77
