module

public import CFSG.RankThree.Native.Co2FiveArrays
public import CFSG.Sporadic.Co2Cert.Data
public meta import CFSG.RankThree.Native.Co2FiveArrays
public meta import CFSG.Sporadic.Co2Cert.Data
public meta import Mathlib.GroupTheory.Schreier
public import Mathlib.GroupTheory.Schreier
public import Std.Data.HashMap

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Native

open CFSG.RankThree.Native CFSG.Sporadic.Co2Cert

@[expose] def dot22 (x y : Nat) : Bool :=
  (List.range 22).foldl (fun acc j => acc ^^ (x.testBit j && y.testBit j)) false

@[expose] def co2LineDiff (r i : Nat) : Nat :=
  co2PackedVecs[(co2FiveLineArr r)[i]!]! ^^^ co2PackedVecs[i]!

@[expose] def co2RankIdx0 : List Nat :=
  [0, 1, 2, 3, 4, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 17, 18, 23, 28, 41]

@[expose] def co2RankDual0 : List Nat :=
  [2184432, 3283360, 864130, 1188726, 351472, 2570256, 1027922, 517894, 3294502, 2500466,
    2403510, 2118020, 1093522, 718020, 1320720, 1099638, 3405076, 22258, 1425298, 382624]

@[expose] def co2RankIdx1 : List Nat :=
  [0, 1, 2, 3, 4, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 17]

@[expose] def co2RankDual1 : List Nat :=
  [3409408, 4106816, 358464, 676928, 2335488, 1876288, 3483520, 732800, 2671232, 1949120,
    3552512, 310976, 468736, 848128, 1321024, 3119232]

@[expose] def co2RankCheckOf (r : Nat) (idx dual : List Nat) : Bool :=
  idx.all (· < 2300) && dual.length == idx.length &&
    (List.range idx.length).all fun k => (List.range idx.length).all fun l =>
      dot22 (dual.getD k 0) (co2LineDiff r (idx.getD l 0)) == (k == l)

@[noinline, expose] def co2RankCheck (_ : Unit := ()) : Bool :=
  co2RankCheckOf 0 co2RankIdx0 co2RankDual0 && co2RankCheckOf 1 co2RankIdx1 co2RankDual1

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Native
