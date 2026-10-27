module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3ZData

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaSec3

open CFSG.Monster.B.Co2.Native CFSG.RankThree.Native CFSG.EvenSmallLie.UnitarySix.YamadaPar
open CFSG.EvenSmallLie.UnitarySix.YamadaD

@[expose] def coordNWit (v : ℕ) : List ℕ :=
  (List.range 8).filterMap fun i =>
    if v / 2 ^ i % 2 = 1 then some ([0, 1, 5, 6, 9, 10, 12, 13] : List ℕ)[i]! else none

@[expose] def coordWWit (v : ℕ) : List ℕ :=
  (List.range 4).filterMap fun i =>
    if v / 2 ^ i % 2 = 1 then some ([11, 12, 13, 14] : List ℕ)[i]! else none

@[expose] def coordNGenCheck : Bool :=
  kNA (idA 693) == 0 && pt1Mask.all (· < 256) &&
    (List.range 256).all fun v => kNA (wA (coordNWit v)) == v

@[expose] def coordNAt (a : Array ℕ) : Bool :=
  (chA1.O.all fun s => kNA (compA 693 a s) == (kNA a ^^^ kNA s)) &&
  ((kNA a == 0) == siftA 693 lvZ chZ.B 0 a) &&
  (List.range 5).all fun j =>
    kNA (conjA 693 chK1.O[j]! a) == bmulVec 8 8 (wedgeGensN.getD j #[]) (kNA a)

@[expose] def coordWGenCheck : Bool := (List.range 16).all fun v => kWA (wA (coordWWit v)) == v

@[expose] def coordWAt (a : Array ℕ) : Bool :=
  (kWA a != 0 || eqA 693 a (idA 693)) &&
  (List.range 3).all fun j =>
    kWA (conjA 693 chLam.O[j]! a) == bmulVec 4 4 (wedgeGensW.getD j #[]) (kWA a)

@[expose] def coordWPairAt (a b : Array ℕ) : Bool := kWA (compA 693 a b) == (kWA a ^^^ kWA b)

end CFSG.EvenSmallLie.UnitarySix.YamadaSec3

end
