module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3XData

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaSec3

open CFSG.Monster.B.Co2.Native CFSG.RankThree.Native

@[expose] def commA (a b : Array ℕ) : Bool := eqA 693 (compA 693 a b) (compA 693 b a)

@[expose] def commPts : List ℕ := [1, 3, 45, 205, 251]

@[expose] def commFail (a s : Array ℕ) : Bool := commPts.any fun p => a[s[p]!]! != s[a[p]!]!

@[expose] def zSAt (a : Array ℕ) : Bool :=
  !(chS.O.all fun s => commA a s) || siftA 693 lvZ chZ.B 0 a

@[expose] def zA3At (a : Array ℕ) : Bool :=
  ((chA3.O.any fun s => commFail a s) || (!(chA3.O.all fun s => commA a s) ||
    siftA 693 lvA4 chA4.B 0 a)) &&
  (commFail a ae || (!(commA a ae) || siftA 693 lvA4 chA4.B 0 a))

@[expose] def a1At (a : Array ℕ) : Bool :=
  (!(chA1.O.all fun s => commA a s) || siftA 693 lvZ chZ.B 0 a) &&
  (!(commA a ae) || siftA 693 lvX1Z chX1Z.B 0 a) &&
  (!(chX6Z.O.all fun s => commA a s) || siftA 693 lvA2 chA2.B 0 a)

@[expose] def a1GenCheck : Bool :=
  (chA1.O.all fun s => siftA 693 lvZ chZ.B 0 (compA 693 s s)) &&
    chA1.O.all fun s => chA1.O.all fun t => siftA 693 lvZ chZ.B 0 (commutatorA 693 s t)

@[expose] def a4At (a : Array ℕ) : Bool :=
  (!(chX1.O.all fun s => commA a s) || siftA 693 lvZ chZ.B 0 a) &&
  (!(siftA 693 lvA1 chA1.B 0 a) || siftA 693 lvZ2S chZ2S.B 0 a) &&
  siftA 693 lvX8 chX8.B 0 (commutatorA 693 a aj₀) &&
  siftA 693 lvX8 chX8.B 0 (commutatorA 693 a aj₀sq)

@[expose] def a4PairAt (y a : Array ℕ) : Bool :=
  eqA 693 y (idA 693) || !(siftA 693 lvZ chZ.B 0 (commutatorA 693 y a)) ||
    siftA 693 lvZ2S chZ2S.B 0 a

@[expose] def z2sAt (b : Array ℕ) : Bool :=
  (!(siftA 693 lvZ2S chZ2S.B 0 (conjA 693 (gA 16) b)) || siftA 693 lvZ chZ.B 0 b) &&
  (!(siftA 693 lvZ2S chZ2S.B 0 (conjA 693 ag232 b)) || siftA 693 lvZ chZ.B 0 b)

@[expose] def z2sPairAt (y b : Array ℕ) : Bool := siftA 693 lvZ chZ.B 0 (commutatorA 693 y b)

@[expose] def a2At (a : Array ℕ) : Bool :=
  !(siftA 693 lvA1 chA1.B 0 a) || siftA 693 lvX6Z chX6Z.B 0 a

@[expose] def labA3 : Array ℕ :=
  #[0, 1, 1, 3, 3, 5, 5, 7, 7, 3, 3, 11, 12, 1, 1, 15, 3, 5, 15, 7,
    3, 5, 5, 15, 15, 3, 5, 27, 1, 1, 15, 5, 7, 7, 7, 15, 15, 7, 3, 15,
    5, 7, 42, 1, 1, 1, 1, 15, 15, 5, 7, 15, 7, 3, 15, 3, 5, 15, 15, 5,
    7, 1, 1, 7, 7, 5, 5, 15, 7, 3, 7, 7, 1, 1, 3, 3, 15, 3, 5, 5,
    5, 3, 3, 1, 1, 1, 1, 15, 15, 5, 7, 15, 7, 3, 15, 3, 5, 15, 15, 5,
    7, 1, 1, 7, 7, 5, 5, 15, 7, 3, 7, 7, 1, 1, 3, 3, 15, 3, 5, 5,
    5, 3, 3, 1, 1, 1, 1, 15, 15, 5, 7, 15, 7, 3, 15, 3, 5, 15, 15, 5,
    7, 1, 1, 7, 7, 5, 5, 15, 7, 3, 7, 7, 1, 1, 3, 3, 15, 3, 5, 5,
    5, 3, 3, 1, 1, 1, 1, 15, 15, 5, 7, 15, 7, 3, 15, 3, 5, 15, 15, 5,
    7, 1, 1, 7, 7, 5, 5, 15, 7, 3, 7, 7, 1, 1, 3, 3, 15, 3, 5, 5,
    5, 3, 3, 1, 1, 205, 205, 1, 1, 3, 3, 5, 5, 7, 7, 3, 3, 205, 205, 1,
    1, 15, 3, 5, 15, 7, 3, 5, 5, 15, 15, 3, 5, 205, 1, 1, 15, 5, 7, 7,
    7, 15, 15, 7, 3, 15, 5, 7, 205, 1, 1, 251, 1, 1, 3, 3, 5, 5, 7, 7,
    3, 3, 251, 251, 1, 1, 15, 3, 5, 15, 7, 3, 5, 5, 15, 15, 3, 5, 251, 1,
    1, 15, 5, 7, 7, 7, 15, 15, 7, 3, 15, 5, 7, 251, 1, 1, 296, 1, 1, 3,
    3, 5, 5, 7, 7, 3, 3, 296, 296, 1, 1, 15, 3, 5, 15, 7, 3, 5, 5, 15,
    15, 3, 5, 296, 1, 1, 15, 5, 7, 7, 7, 15, 15, 7, 3, 15, 5, 7, 296, 1,
    1, 1, 1, 15, 15, 5, 7, 15, 7, 3, 15, 3, 5, 15, 15, 5, 7, 1, 1, 7,
    7, 5, 5, 15, 7, 3, 7, 7, 1, 1, 3, 3, 15, 3, 5, 5, 5, 3, 3, 1,
    1, 296, 296, 1, 1, 3, 3, 5, 5, 7, 7, 3, 3, 296, 296, 1, 1, 15, 3, 5,
    15, 7, 3, 5, 5, 15, 15, 3, 5, 296, 1, 1, 15, 5, 7, 7, 7, 15, 15, 7,
    3, 15, 5, 7, 296, 1, 1, 205, 1, 1, 3, 3, 5, 5, 7, 7, 3, 3, 205, 205,
    1, 1, 15, 3, 5, 15, 7, 3, 5, 5, 15, 15, 3, 5, 205, 1, 1, 15, 5, 7,
    7, 7, 15, 15, 7, 3, 15, 5, 7, 205, 1, 1, 251, 1, 1, 3, 3, 5, 5, 7,
    7, 3, 3, 251, 251, 1, 1, 15, 3, 5, 15, 7, 3, 5, 5, 15, 15, 3, 5, 251,
    1, 1, 15, 5, 7, 7, 7, 15, 15, 7, 3, 15, 5, 7, 251, 1, 1, 1, 1, 15,
    15, 5, 7, 15, 7, 3, 15, 3, 5, 15, 15, 5, 7, 1, 1, 7, 7, 5, 5, 15,
    7, 3, 7, 7, 1, 1, 3, 3, 15, 3, 5, 5, 5, 3, 3, 1, 1, 251, 251, 1,
    1, 3, 3, 5, 5, 7, 7, 3, 3, 251, 251, 1, 1, 15, 3, 5, 15, 7, 3, 5,
    5, 15, 15, 3, 5, 251, 1, 1, 15, 5, 7, 7, 7, 15, 15, 7, 3, 15, 5, 7,
    251, 1, 1, 296, 1, 1, 3, 3, 5, 5, 7, 7, 3, 3, 296, 296, 1, 1, 15, 3,
    5, 15, 7, 3, 5, 5, 15, 15, 3, 5, 296, 1, 1, 15, 5, 7, 7, 7, 15, 15,
    7, 3, 15, 5, 7, 296, 1, 1, 205, 1, 1, 3, 3, 5, 5, 7, 7, 3, 3, 205,
    205, 1, 1, 15, 3, 5, 15, 7, 3, 5, 5, 15, 15, 3, 5, 205, 1, 1, 15, 5,
    7, 7, 7, 15, 15, 7, 3, 15, 5, 7, 205, 1, 1]

@[expose] def labA3Check : Bool :=
  labA3.size == 693 && chA3.O.all fun g => allLt 693 fun p => labA3[g[p]!]! == labA3[p]!

@[expose] def p2At (a : Array ℕ) : Bool :=
  !(chA3.O.all fun s => labA3[a[s[2]!]!]! == labA3[a[2]!]!) ||
    !(chA3.O.all fun s => siftA 693 lvA3 chA3.B 0 (conjA 693 a s)) || siftA 693 lvP2 chP2.B 0 a

end CFSG.EvenSmallLie.UnitarySix.YamadaSec3

end
