module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3HAData

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaSec3

open CFSG.Monster.B.Co2.Native CFSG.RankThree.Native

@[expose] def labA1 : Array ℕ :=
  #[0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 11, 11, 1, 1, 15, 1, 1, 18, 1,
    1, 1, 1, 18, 18, 1, 1, 11, 1, 1, 15, 1, 1, 1, 1, 15, 15, 1, 1, 18,
    1, 1, 11, 1, 1, 1, 1, 47, 47, 1, 1, 51, 1, 1, 54, 1, 1, 57, 57, 1,
    1, 1, 1, 1, 1, 1, 1, 67, 1, 1, 1, 1, 1, 1, 1, 1, 76, 1, 1, 1,
    1, 1, 1, 1, 1, 1, 1, 54, 54, 1, 1, 47, 1, 1, 51, 1, 1, 76, 76, 1,
    1, 1, 1, 1, 1, 1, 1, 57, 1, 1, 1, 1, 1, 1, 1, 1, 67, 1, 1, 1,
    1, 1, 1, 1, 1, 1, 1, 51, 51, 1, 1, 54, 1, 1, 47, 1, 1, 67, 67, 1,
    1, 1, 1, 1, 1, 1, 1, 76, 1, 1, 1, 1, 1, 1, 1, 1, 57, 1, 1, 1,
    1, 1, 1, 1, 1, 1, 1, 167, 167, 1, 1, 171, 1, 1, 174, 1, 1, 177, 177, 1,
    1, 1, 1, 1, 1, 1, 1, 187, 1, 1, 1, 1, 1, 1, 1, 1, 196, 1, 1, 1,
    1, 1, 1, 1, 1, 205, 205, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 217, 217, 1,
    1, 221, 1, 1, 224, 1, 1, 1, 1, 229, 229, 1, 1, 233, 1, 1, 236, 1, 1, 1,
    1, 241, 241, 1, 1, 245, 1, 1, 248, 1, 1, 251, 1, 1, 1, 1, 1, 1, 1, 1,
    1, 1, 262, 262, 1, 1, 266, 1, 1, 269, 1, 1, 1, 1, 274, 274, 1, 1, 278, 1,
    1, 281, 1, 1, 1, 1, 286, 286, 1, 1, 290, 1, 1, 293, 1, 1, 296, 1, 1, 1,
    1, 1, 1, 1, 1, 1, 1, 307, 307, 1, 1, 311, 1, 1, 314, 1, 1, 1, 1, 319,
    319, 1, 1, 323, 1, 1, 326, 1, 1, 1, 1, 331, 331, 1, 1, 335, 1, 1, 338, 1,
    1, 1, 1, 174, 174, 1, 1, 167, 1, 1, 171, 1, 1, 196, 196, 1, 1, 1, 1, 1,
    1, 1, 1, 177, 1, 1, 1, 1, 1, 1, 1, 1, 187, 1, 1, 1, 1, 1, 1, 1,
    1, 296, 296, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 338, 338, 1, 1, 331, 1, 1,
    335, 1, 1, 1, 1, 314, 314, 1, 1, 307, 1, 1, 311, 1, 1, 1, 1, 326, 326, 1,
    1, 319, 1, 1, 323, 1, 1, 205, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 248, 248,
    1, 1, 241, 1, 1, 245, 1, 1, 1, 1, 224, 224, 1, 1, 217, 1, 1, 221, 1, 1,
    1, 1, 236, 236, 1, 1, 229, 1, 1, 233, 1, 1, 251, 1, 1, 1, 1, 1, 1, 1,
    1, 1, 1, 293, 293, 1, 1, 286, 1, 1, 290, 1, 1, 1, 1, 269, 269, 1, 1, 262,
    1, 1, 266, 1, 1, 1, 1, 281, 281, 1, 1, 274, 1, 1, 278, 1, 1, 1, 1, 171,
    171, 1, 1, 174, 1, 1, 167, 1, 1, 187, 187, 1, 1, 1, 1, 1, 1, 1, 1, 196,
    1, 1, 1, 1, 1, 1, 1, 1, 177, 1, 1, 1, 1, 1, 1, 1, 1, 251, 251, 1,
    1, 1, 1, 1, 1, 1, 1, 1, 1, 278, 278, 1, 1, 281, 1, 1, 274, 1, 1, 1,
    1, 290, 290, 1, 1, 293, 1, 1, 286, 1, 1, 1, 1, 266, 266, 1, 1, 269, 1, 1,
    262, 1, 1, 296, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 323, 323, 1, 1, 326, 1,
    1, 319, 1, 1, 1, 1, 335, 335, 1, 1, 338, 1, 1, 331, 1, 1, 1, 1, 311, 311,
    1, 1, 314, 1, 1, 307, 1, 1, 205, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 233,
    233, 1, 1, 236, 1, 1, 229, 1, 1, 1, 1, 245, 245, 1, 1, 248, 1, 1, 241, 1,
    1, 1, 1, 221, 221, 1, 1, 224, 1, 1, 217, 1, 1]

@[expose] def labA1Check : Bool :=
  labA1.size == 693 && chA1.O.all fun g => allLt 693 fun p => labA1[g[p]!]! == labA1[p]!

@[expose] def c8WitL (k d : Array ℕ) : Bool :=
  chK1.O.any fun g => !(allLt 693 fun p => labA1[k[d[g[p]!]!]!]! == labA1[g[k[d[p]!]!]!]!)

@[expose] def c10At (k : Array ℕ) : Bool :=
  allLt 6 fun q => c10Wit k dArr[q]! || (q == 0 && eqA 693 k (idA 693))

@[expose] def c8At (k : Array ℕ) : Bool :=
  allLt 6 fun q => q == 1 || q == 2 || c8WitL k dArr[q]! || (q == 0 && eqA 693 k (idA 693))

@[expose] def z2sW : List (List ℕ) :=
  [[], [12], [13], [14], [12, 13], [12, 14], [13, 14], [12, 13, 14]]

@[expose] def c11RejW (k : Array ℕ) : Bool :=
  chZ2S.O.any fun g => !(allLt 693 fun p => z2sW.any fun w => k[g[p]!]! == (wA w)[k[p]!]!)

@[expose] def c11bAt (k : Array ℕ) : Bool := c11RejW k || siftA 693 lvP2 chP2.B 0 k

@[expose] def z2sKeyAt (b : Array ℕ) : Bool :=
  (b[1]! != 1 || eqA 693 b (idA 693)) && (z2sW.map fun w => (wA w)[1]!).contains b[1]!

@[expose] def c11aAt (b : Array ℕ) : Bool := eqA 693 b gz || fixCnt b != fixCnt gz

@[expose] def c6At (l : Array ℕ) : Bool :=
  [0, 3].all fun q =>
    !(chA4.O.all fun g => eqA 693 (compA 693 (compA 693 l dArr[q]!) g)
      (compA 693 g (compA 693 l dArr[q]!))) || (q == 0 && eqA 693 l (idA 693))

@[expose] def c7PtW (l s d g : Array ℕ) : Bool :=
  fixF.any fun p => (compA 693 (compA 693 (compA 693 (compA 693 l s) d) g)
    (compA 693 (compA 693 (compA 693 (invCand 693 d) (invCand 693 s)) (invCand 693 l))
      (invCand 693 g)))[p]! != p

@[expose] def c7At (l s : Array ℕ) : Bool :=
  allLt 6 fun q =>
    (lsGens.any fun g => c7PtW l s dArr[q]! g) ||
    (eqA 693 l (idA 693) && eqA 693 s (idA 693) && q < 3) ||
    !(lsGens.all fun g => siftA 693 lvA3 chA3.B 0
      (commutatorA 693 (compA 693 (compA 693 l s) dArr[q]!) g))

@[expose] def c9At (s : Array ℕ) : Bool :=
  eqA 693 s (idA 693) ||
    !(chSig.O.all fun g => siftA 693 lvA3 chA3.B 0 (commutatorA 693 s g))

@[expose] def i5GenCheck : Bool :=
  validA 693 (wA [16, 17, 16, 17]) &&
    chA1.O.all fun a => siftA 693 lvS chS.B 0 (conjInvA 693 (wA [16, 17, 16, 17]) a)

@[expose] def i5At (t : Array ℕ) : Bool :=
  !(siftA 693 lvS chS.B 0 (conjInvA 693 (wA [16, 17, 16, 17]) t)) || siftA 693 lvA1 chA1.B 0 t

@[expose] def i8GenCheck : Bool :=
  validA 693 (wA [15, 17]) &&
    (chA3.O.all fun a => siftA 693 lvS chS.B 0 (conjInvA 693 (wA [15, 17]) a)) &&
    (chX1.O.all fun x => chX3A3.O.all fun g => siftA 693 lvX3A3 chX3A3.B 0 (conjA 693 x g)) &&
    chX3.O.all fun x => chA3.O.all fun g => siftA 693 lvA3 chA3.B 0 (conjA 693 x g)

@[expose] def i8At (x y : Array ℕ) : Bool :=
  !(siftA 693 lvS chS.B 0 (conjInvA 693 (wA [15, 17]) (compA 693 x y))) ||
    siftA 693 lvA3 chA3.B 0 (compA 693 x y)

@[expose] def i8bGenCheck : Bool :=
  validA 693 (wA [4, 17]) &&
    chA3.O.all fun a => siftA 693 lvX3A3 chX3A3.B 0 (conjInvA 693 (wA [4, 17]) a)

@[expose] def i8bAt (y : Array ℕ) : Bool :=
  !(siftA 693 lvX3A3 chX3A3.B 0 (conjInvA 693 (wA [4, 17]) y)) || siftA 693 lvA3 chA3.B 0 y

end CFSG.EvenSmallLie.UnitarySix.YamadaSec3

end
