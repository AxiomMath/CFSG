module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaHAutData

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaSec3

open CFSG.Fischer CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2
open CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native
open CFSG.EvenSmallLie.UnitarySix.YamadaHAut (dTab sTab d2Tab dsTab d2sTab)

@[expose] def dArr : Array (Array ℕ) := #[idA 693, dTab, d2Tab, sTab, dsTab, d2sTab]

@[expose] def gz : Array ℕ := gA 14

@[expose] def chX3A3 : ChainData where
  gens := [[4], [2], [3], [5], [6], [7], [8], [9], [10], [11], [12], [13], [14]]
  words := [[-2, 7], [-6, 11], [-3, 12], [-1, -3, 6, 1], [-10, -15, -13, 8, 1]]
  base := [45, 3, 1]

@[expose] def chSigA3 : ChainData where
  gens := [[4], [17], [2], [3], [5], [6], [7], [8], [9], [10], [11], [12], [13], [14]]
  words := [[-3, 8], [-7, 12], [-4, 13], [-1, -4, 7, 1], [-11, -16, -14, 9, 1],
    [-16, 18, -10, 6, 2]]
  base := [45, 3, 1]

@[expose] def lvX3A3 : Array Level := chX3A3.levels
@[expose] def lvSigA3 : Array Level := chSigA3.levels

@[expose] def eLam : ArrCert := enumBfs 693 chLam.O chLam.base 100

@[expose] def eSig : ArrCert := enumBfs 693 chSig.O chSig.base 20

@[expose] def eX3A3 : ArrCert := enumBfs 693 chX3A3.O chX3A3.base 10000

@[expose] def labStep (gs : Array (Array ℕ)) (lab : Array ℕ) : Array ℕ :=
  gs.foldl (fun lab g => (List.range 693).foldl (fun lab p =>
    let a := lab[p]!
    let b := lab[g[p]!]!
    if b < a then lab.set! p b else if a < b then lab.set! g[p]! a else lab) lab) lab

@[expose] def labFix (gs : Array (Array ℕ)) : ℕ → Array ℕ → Array ℕ
  | 0, lab => lab
  | n + 1, lab =>
    let lab' := labStep gs lab
    if lab' == lab then lab else labFix gs n lab'

@[expose] def lab1 : Array ℕ := labFix chA1.O 700 (Array.range 693)

@[expose] def lab1Check : Bool :=
  lab1.size == 693 && chA1.O.all fun g => allLt 693 fun p => lab1[g[p]!]! == lab1[p]!

@[expose] def c10Wit (k d : Array ℕ) : Bool :=
  chA1.O.any fun g => !(allLt 693 fun p =>
    let r := g[k[d[p]!]!]!
    let l := k[d[g[p]!]!]!
    l == r || l == gz[r]!)

@[expose] def c10Check : Bool :=
  allLt eK1.pts.size fun m => allLt 6 fun q =>
    (q == 0 && eqA 693 eK1.pts[m]! (idA 693)) || c10Wit eK1.pts[m]! dArr[q]!

@[expose] def c8Wit (k d : Array ℕ) : Bool :=
  chK1.O.any fun g => !(allLt 693 fun p => lab1[k[d[g[p]!]!]!]! == lab1[g[k[d[p]!]!]!]!)

@[expose] def c8Check : Bool :=
  allLt eK1.pts.size fun m => allLt 6 fun q =>
    q == 1 || q == 2 || (q == 0 && eqA 693 eK1.pts[m]! (idA 693)) || c8Wit eK1.pts[m]! dArr[q]!

@[expose] def fixCnt (a : Array ℕ) : ℕ := (List.range 693).countP fun p => a[p]! == p

@[expose] def c11aCheck : Bool :=
  allLt eZ2S.pts.size fun m => eqA 693 eZ2S.pts[m]! gz || fixCnt eZ2S.pts[m]! != fixCnt gz

@[expose] def c11Rej (k : Array ℕ) : Bool :=
  chZ2S.O.any fun g => !(allLt 693 fun p => eZ2S.pts.any fun b => k[g[p]!]! == b[k[p]!]!)

@[expose] def c11bCheck : Bool :=
  allLt eK1.pts.size fun m => c11Rej eK1.pts[m]! || siftA 693 lvP2 chP2.B 0 eK1.pts[m]!

@[expose] def lsGens : Array (Array ℕ) := chLam.O ++ chSig.O

@[expose] def c6Check : Bool :=
  allLt eLam.pts.size fun l => [0, 3].all fun q =>
    (q == 0 && eqA 693 eLam.pts[l]! (idA 693)) ||
      !(chA4.O.all fun g => eqA 693 (compA 693 (compA 693 eLam.pts[l]! dArr[q]!) g)
        (compA 693 g (compA 693 eLam.pts[l]! dArr[q]!)))

@[expose] def c7Check : Bool :=
  allLt eLam.pts.size fun l => allLt eSig.pts.size fun s => allLt 6 fun q =>
    (eqA 693 eLam.pts[l]! (idA 693) && eqA 693 eSig.pts[s]! (idA 693) && q < 3) ||
      (validA 693 (compA 693 (compA 693 eLam.pts[l]! eSig.pts[s]!) dArr[q]!) &&
        !(lsGens.all fun g => siftA 693 lvA3 chA3.B 0
          (commutatorA 693 (compA 693 (compA 693 eLam.pts[l]! eSig.pts[s]!) dArr[q]!) g)))

@[expose] def c9Check : Bool :=
  allLt eSig.pts.size fun s => eqA 693 eSig.pts[s]! (idA 693) ||
    !(chSig.O.all fun g => siftA 693 lvA3 chA3.B 0 (commutatorA 693 eSig.pts[s]! g))

@[expose] def i5Check : Bool :=
  validA 693 (wA [16, 17, 16, 17]) &&
  allLt eS.pts.size fun m =>
    !(siftA 693 lvS chS.B 0 (conjInvA 693 (wA [16, 17, 16, 17]) eS.pts[m]!)) ||
      siftA 693 lvA1 chA1.B 0 eS.pts[m]!

@[expose] def i8Check : Bool :=
  validA 693 (wA [15, 17]) &&
  allLt eS.pts.size fun m =>
    !(siftA 693 lvS chS.B 0 (conjInvA 693 (wA [15, 17]) eS.pts[m]!)) ||
      siftA 693 lvA3 chA3.B 0 eS.pts[m]!

@[expose] def i8bCheck : Bool :=
  validA 693 (wA [4, 17]) &&
  allLt eX3A3.pts.size fun m =>
    !(siftA 693 lvX3A3 chX3A3.B 0 (conjInvA 693 (wA [4, 17]) eX3A3.pts[m]!)) ||
      siftA 693 lvA3 chA3.B 0 eX3A3.pts[m]!

@[expose] def nmCheck : Bool :=
  chP2.O.all (validA 693) &&
  (chA1.O.all fun a => chZ2S.O.all fun g => siftA 693 lvZ2S chZ2S.B 0 (conjA 693 a g)) &&
    (chA1.O.all fun a => chA4.O.all fun g => siftA 693 lvA4 chA4.B 0 (conjA 693 a g)) &&
    (chP2.O.all fun a => chA4.O.all fun g => siftA 693 lvA4 chA4.B 0 (conjA 693 a g))

end CFSG.EvenSmallLie.UnitarySix.YamadaSec3
