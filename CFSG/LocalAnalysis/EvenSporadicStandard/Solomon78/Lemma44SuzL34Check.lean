module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocBSSuzCheck
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourCertificate
public meta import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocBSSuzCheck
public meta import CFSG.LocalAnalysis.ComponentClassification.PSL3FourCertificate

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open CFSG.PSL3Four.Native

@[expose] def suzL34Pts : Array Nat :=
  #[22, 1110, 1103, 892, 933, 1151, 1173, 534, 1382, 1181, 774, 509, 1289, 153, 1740, 468,
    1035, 1516, 1418, 1493, 642, 1033, 793, 1213, 680, 1623, 1667, 62, 94, 1185, 639, 1420,
    654, 32, 410, 1013, 118, 1548, 479, 1561, 1533, 306]

@[expose] def suzL34Index (x : Nat) : Nat :=
  ((List.range 42).find? fun i => suzL34Pts[i]! == x).getD 0

@[expose, irreducible] def suzL34TA : Array Nat :=
  Array.ofFn (n := 42) fun i => suzL34Index (suzArrA[suzL34Pts[i.val]!]!)

@[expose, irreducible] def suzL34TB : Array Nat :=
  Array.ofFn (n := 42) fun i => suzL34Index (suzArrB[suzL34Pts[i.val]!]!)

@[expose] def suzL34G1 : List Nat :=
  [2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1,
   1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2]

@[expose] def suzL34G2 : List Nat :=
  [1, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2,
   2, 1, 1, 2, 1]

@[expose] def suzL34G3 : List Nat :=
  [2, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 2, 1, 1, 2,
   2, 1, 2, 1, 2]

@[expose] def suzL34GenTab (l : Nat) : Array Nat :=
  if l = 1 then suzL34TA else suzL34TB

@[expose] def suzL34WordTab (w : List Nat) : Array Nat :=
  w.foldl (fun acc l => comp 42 acc (suzL34GenTab l)) (idTab 42)

@[expose] def suzL34PtsOK : Bool :=
  (suzL34Pts.size == 42) && (List.range 42).all (fun i => suzL34Pts[i]! < 1782) &&
    decide suzL34Pts.toList.Nodup

@[expose] def suzL34RestrOK (t g : Array Nat) : Bool :=
  (List.range 42).all fun i =>
    (t[i]! < 42) && (suzL34Pts[t[i]!]! == g[suzL34Pts[i]!]!)

@[expose] def suzL34WordsOK : Bool :=
  (suzL34WordTab suzL34G1 == g₁T) && (suzL34WordTab suzL34G2 == g₂T) &&
    (suzL34WordTab suzL34G3 == g₃T)

@[expose] def suzL34Check : Bool :=
  suzL34PtsOK && suzL34RestrOK suzL34TA suzArrA && suzL34RestrOK suzL34TB suzArrB &&
    suzL34WordsOK

end CFSG.EvenSporadicStandard.Solomon78
