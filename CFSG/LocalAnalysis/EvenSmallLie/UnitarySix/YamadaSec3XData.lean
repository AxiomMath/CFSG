module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3Data
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.NativeDataBase

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaSec3

open CFSG.Fischer CFSG.F4.Native CFSG.Certificates CFSG.Certificates.Native
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native

@[expose] def chA3 : ChainData where
  gens := [[2], [3], [5], [6], [7], [8], [9], [10], [11], [12], [13], [14]]
  words := [[-1, 3], [-2, 4], [-5, 7], [-6, 8]]
  base := [3, 1]

@[expose] def chA4 : ChainData where
  gens := [[11], [12], [13], [14]]
  words := [[-4, 2, 1]]
  base := [3, 1]

@[expose] def chX8 : ChainData where
  gens := [[12], [13]]
  words := []
  base := [1]

@[expose] def chSig : ChainData where
  gens := [[4], [17]]
  words := []
  base := [45]

@[expose] def chLam : ChainData where
  gens := [[0], [1], [15]]
  words := [[-1, 3, 1], [-1, -2, 3, 2], [-4, 5, 4]]
  base := [1, 0, 3]

@[expose] def chZ2S : ChainData where
  gens := [[12], [13], [14]]
  words := []
  base := [1]

@[expose] def chX6Z : ChainData where
  gens := [[9], [10], [12], [13], [14]]
  words := []
  base := [1]

@[expose] def chZ : ChainData where
  gens := [[14]]
  words := []
  base := [1]

@[expose] def chX1Z : ChainData where
  gens := [[0], [1], [12], [13], [14]]
  words := []
  base := [1]

@[expose] def chP2 : ChainData where
  gens := [[0], [1], [15], [4], [17], [2], [3], [5], [6], [7], [8], [9], [10], [11], [12], [13],
    [14]]
  words := [[-6, 11], [-4, -7, 10, 4], [-6, -1, 3, 1], [-5, -4, -6, -1, -2, 3, 2]]
  base := [1, 45, 3]

@[expose] def lvA3 : Array Level := chA3.levels
@[expose] def lvA4 : Array Level := chA4.levels
@[expose] def lvX8 : Array Level := chX8.levels
@[expose] def lvSig : Array Level := chSig.levels
@[expose] def lvLam : Array Level := chLam.levels
@[expose] def lvZ2S : Array Level := chZ2S.levels
@[expose] def lvX6Z : Array Level := chX6Z.levels
@[expose] def lvZ : Array Level := chZ.levels
@[expose] def lvX1Z : Array Level := chX1Z.levels
@[expose] def lvP2 : Array Level := chP2.levels

@[expose] def eA3 : ArrCert := enumBfs 693 chA3.O chA3.base 5000

@[expose] def eA4 : ArrCert := enumBfs 693 chA4.O chA4.base 100

@[expose] def eZ2S : ArrCert := enumBfs 693 chZ2S.O chZ2S.base 100

@[expose] def eX1 : ArrCert := enumBfs 693 chX1.O chX1.base 100

@[expose] def ae : Array ℕ := wA [4, 17]

@[expose] def aj₀sq : Array ℕ := wA [15, 1, 15, 0, 1, 15, 1, 15, 1, 15, 0, 1, 15, 1]

@[expose] def ag232 : Array ℕ := wA [16, 17, 16]

@[expose] def fixF : List ℕ := [0, 11, 12, 27, 42]

@[expose] def qF : List (List ℕ) := [[], [15], [15, 0], [15, 1], [15, 0, 1]]

@[expose] def xIds : List (List ℕ × List ℕ) := [([0, 0], []), ([1, 1], []), ([2, 2], []),
    ([3, 3], []), ([4, 4], []), ([5, 5], []), ([6, 6], []), ([7, 7], []), ([8, 8], []),
    ([9, 9], []), ([10, 10], []), ([11, 11], []), ([12, 12], []), ([13, 13], []), ([14, 14], []),
    ([15, 15], []), ([16, 16], []), ([17, 17], []), ([4, 17, 4, 17, 4, 17], []),
    ([15, 1, 15, 0, 1, 15, 1, 15, 1, 15, 0, 1, 15, 1, 15, 1, 15, 0, 1, 15, 1], []),
    ([15, 1, 15, 0, 1, 15, 1, 0, 1, 15, 1, 0, 15, 1, 15], [1]),
    ([15, 1, 15, 0, 1, 15, 1, 1, 1, 15, 1, 0, 15, 1, 15], [0, 1]), ([0, 1], [1, 0]),
    ([15, 1, 15, 0, 1, 15, 1, 14], [14, 15, 1, 15, 0, 1, 15, 1]),
    ([15, 1, 15, 0, 1, 15, 1, 11], [11, 15, 1, 15, 0, 1, 15, 1]),
    ([11, 0, 11, 0, 1, 11, 1, 0, 1, 11, 1, 0], [14]),
    ([15, 1, 15, 0, 1, 15, 1, 4, 17], [4, 17, 15, 1, 15, 0, 1, 15, 1]),
    ([16, 17, 16, 16, 17, 16], []), ([16, 17, 16, 4, 17], [4, 17, 16, 17, 16]),
    ([16, 17, 16, 15, 1, 15, 0, 1, 15, 1], [15, 1, 15, 0, 1, 15, 1, 16, 17, 16]),
    ([16, 17, 16, 12, 16, 17, 16], [0]), ([16, 17, 16, 13, 16, 17, 16], [1]), ([16, 12, 16], [9]),
    ([16, 13, 16], [10]), ([16, 14, 16], [14]),
    ([11, 15, 1, 15, 0, 1, 15, 1], [15, 1, 15, 0, 1, 15, 1, 11])]

@[expose] def cwW (a b : List ℕ) : List ℕ := a ++ b ++ a.reverse ++ b.reverse

@[expose] def cjW (a b : List ℕ) : List ℕ := a ++ b ++ a.reverse

@[expose] def prodWord (f : List ℕ → List ℕ → List ℕ) (bs : List (List ℕ × List ℕ)) : List ℕ :=
  bs.flatMap fun b => f b.1 b.2

@[expose] def prodCheck (f : List ℕ → List ℕ → List ℕ) (data : List (ℕ × List (List ℕ × List ℕ))) :
    Bool :=
  data.all fun p => eqA 693 (wA [p.1]) (wA (prodWord f p.2))

@[expose] def a4cData : List (ℕ × List (List ℕ × List ℕ)) := [(11, [([12], [15, 1])]),
    (12, [([13], [15])]), (13, [([12, 11], [1])]), (14, [([12], [1])])]

@[expose] def a4aData : List (ℕ × List (List ℕ × List ℕ)) := [(11, [([], [11])]),
    (12, [([1], [11]), ([1, 0], [11])]), (13, [([0], [11]), ([1, 0], [11])]),
    (14, [([], [11]), ([0], [11]), ([1], [11]), ([1, 0], [11])])]

@[expose] def a4zData : List (ℕ × List (List ℕ × List ℕ)) := [(11, [([15], [14])]),
    (12, [([1, 15], [14]), ([1, 0, 15], [14])]), (13, [([0, 15], [14]), ([1, 0, 15], [14])]),
    (14, [([], [14])])]

@[expose] def a4jData : List (ℕ × List (List ℕ × List ℕ)) := [
    (12, [([13], [15, 1, 15, 0, 1, 15, 1])]), (13, [([13, 12], [15, 1, 15, 0, 1, 15, 1])])]

@[expose] def k1pData : List (ℕ × List (List ℕ × List ℕ)) := [(2, [([3], [17, 16, 17])]),
    (3, [([17, 4, 2], [4, 3, 4])]), (4, [([16, 3], [17, 2, 17])]),
    (16, [([2, 16, 3], [17, 16, 17])]), (17, [([2], [4, 3, 4]), ([17], [16, 17, 4])])]

@[expose] def a1cData : List (ℕ × List (List ℕ × List ℕ)) := [(0, [([], [0])]), (1, [([], [1])]),
    (5, [([], [0]), ([2], [0])]), (6, [([], [0]), ([3], [0])]), (9, [([], [0]), ([7], [0])]),
    (10, [([], [0]), ([8], [0])]), (12, [([], [0]), ([13, 11], [0])]),
    (13, [([], [1]), ([12, 11], [1])]), (14, [([], [0]), ([13], [0])])]

@[expose] def a2cData : List (ℕ × List (List ℕ × List ℕ)) := [(4, [([16], [11])]),
    (7, [([3, 16], [11]), ([3, 2, 16], [11])]), (8, [([2, 16], [11]), ([3, 2, 16], [11])]),
    (9, [([16], [12])]), (10, [([16], [13])]), (11, [([], [11])]), (12, [([], [12])]),
    (13, [([], [13])]), (14, [([], [14])])]

@[expose] def a12cData : List (ℕ × List (List ℕ × List ℕ)) := [(9, [([0], [7])]),
    (10, [([0], [8])]), (12, [([5], [7])]), (13, [([6], [7])]), (14, [([0], [13])])]

@[expose] def a3eData : List (ℕ × List ℕ × List ℕ) := [(2, [7], [11]), (3, [8], [11]),
    (5, [9], [14]), (6, [10], [14]), (7, [7, 2], [11]), (8, [8, 3], [11]), (9, [9, 5], [14]),
    (10, [10, 6], [14])]

@[expose] def xWitCheck : Bool :=
  prodCheck cwW a4cData && prodCheck cjW a4aData && prodCheck cjW a4zData &&
    prodCheck cwW a4jData && prodCheck cwW k1pData && prodCheck cjW a1cData &&
    prodCheck cjW a2cData && prodCheck cwW a12cData &&
    a3eData.all fun p => eqA 693 (wA [p.1]) (wA (cwW p.2.1 [4, 17] ++ p.2.2))


@[expose] def nativeA : List (Array ℕ) :=
  aWords.map fun w => w.foldr (fun c acc => compA 693 (letterArrs[c.natAbs - 1]!) acc) (idA 693)

@[expose] def xIdCheck : Bool := xIds.all fun p => eqA 693 (wA p.1) (wA p.2)

@[expose] def commCheck (as bs : List (List ℕ)) : Bool :=
  as.all fun a => bs.all fun b => eqA 693 (wA (a ++ b)) (wA (b ++ a))

@[expose] def xCommCheck : Bool :=
  commCheck chA2.gens chA2.gens && commCheck chA3.gens chA4.gens && commCheck [[4, 17]] chA4.gens &&
    commCheck chSig.gens chA4.gens && commCheck chLam.gens chSig.gens &&
    commCheck chK1.gens [[14]] && commCheck chS.gens [[14]] && commCheck chA1.gens [[14]]

@[expose] def xNormCheck : Bool :=
  chLam.O.all (fun x => chA4.O.all fun a => siftA 693 lvA4 chA4.B 0 (conjA 693 x a)) &&
    (chLam.O ++ chSig.O ++ #[ae, aj₀]).all
      (fun x => chA3.O.all fun a => siftA 693 lvA3 chA3.B 0 (conjA 693 x a))

@[expose] def xFixCheck : Bool :=
  allLt 693 (fun p => fixF.contains p == chA3.O.all fun a => a[p]! == p) &&
    (List.range 5).all fun i => (wA qF[i]!)[fixF[i]!]! == 0

@[expose] def zSCheck : Bool :=
  allLt eA2.pts.size fun i =>
    !(chS.O.all fun s => eqA 693 (compA 693 eA2.pts[i]! s) (compA 693 s eA2.pts[i]!)) ||
      siftA 693 lvZ chZ.B 0 eA2.pts[i]!

@[expose] def zA3Check : Bool :=
  allLt eA3.pts.size fun i =>
    (!(chA3.O.all fun s => eqA 693 (compA 693 eA3.pts[i]! s) (compA 693 s eA3.pts[i]!)) ||
      siftA 693 lvA4 chA4.B 0 eA3.pts[i]!) &&
    (!(eqA 693 (compA 693 eA3.pts[i]! ae) (compA 693 ae eA3.pts[i]!)) ||
      siftA 693 lvA4 chA4.B 0 eA3.pts[i]!)

@[expose] def a1Check : Bool :=
  allLt eA1.pts.size fun i =>
    (!(chA1.O.all fun s => eqA 693 (compA 693 eA1.pts[i]! s) (compA 693 s eA1.pts[i]!)) ||
      siftA 693 lvZ chZ.B 0 eA1.pts[i]!) &&
    siftA 693 lvZ chZ.B 0 (compA 693 eA1.pts[i]! eA1.pts[i]!) &&
    (chA1.O.all fun s => siftA 693 lvZ chZ.B 0 (commutatorA 693 eA1.pts[i]! s)) &&
    (!(eqA 693 (compA 693 eA1.pts[i]! ae) (compA 693 ae eA1.pts[i]!)) ||
      siftA 693 lvX1Z chX1Z.B 0 eA1.pts[i]!) &&
    (!(chX6Z.O.all fun s => eqA 693 (compA 693 eA1.pts[i]! s) (compA 693 s eA1.pts[i]!)) ||
      siftA 693 lvA2 chA2.B 0 eA1.pts[i]!)

@[expose] def a4Check : Bool :=
  allLt eA4.pts.size fun i =>
    (!(chX1.O.all fun s => eqA 693 (compA 693 eA4.pts[i]! s) (compA 693 s eA4.pts[i]!)) ||
      siftA 693 lvZ chZ.B 0 eA4.pts[i]!) &&
    (!(siftA 693 lvA1 chA1.B 0 eA4.pts[i]!) || siftA 693 lvZ2S chZ2S.B 0 eA4.pts[i]!) &&
    siftA 693 lvX8 chX8.B 0 (commutatorA 693 eA4.pts[i]! aj₀) &&
    siftA 693 lvX8 chX8.B 0 (commutatorA 693 eA4.pts[i]! aj₀sq) &&
    (allLt eX1.pts.size fun j => eqA 693 eX1.pts[j]! (idA 693) ||
      !(siftA 693 lvZ chZ.B 0 (commutatorA 693 eX1.pts[j]! eA4.pts[i]!)) ||
      siftA 693 lvZ2S chZ2S.B 0 eA4.pts[i]!)

@[expose] def z2sCheck : Bool :=
  allLt eZ2S.pts.size fun i =>
    (allLt eX1.pts.size fun j =>
      siftA 693 lvZ chZ.B 0 (commutatorA 693 eX1.pts[j]! eZ2S.pts[i]!)) &&
    (!(siftA 693 lvZ2S chZ2S.B 0 (conjA 693 (gA 16) eZ2S.pts[i]!)) ||
      siftA 693 lvZ chZ.B 0 eZ2S.pts[i]!) &&
    (!(siftA 693 lvZ2S chZ2S.B 0 (conjA 693 ag232 eZ2S.pts[i]!)) ||
      siftA 693 lvZ chZ.B 0 eZ2S.pts[i]!)

@[expose] def a2Check : Bool :=
  allLt eA2.pts.size fun i =>
    !(siftA 693 lvA1 chA1.B 0 eA2.pts[i]!) || siftA 693 lvX6Z chX6Z.B 0 eA2.pts[i]!

@[expose] def p2Check : Bool :=
  allLt eK1.pts.size fun i =>
    !(chA3.O.all fun a => siftA 693 lvA3 chA3.B 0 (conjA 693 eK1.pts[i]! a)) ||
      siftA 693 lvP2 chP2.B 0 eK1.pts[i]!

@[expose] def uACheck : Bool :=
  validA 693 ae && validA 693 aj₀sq && validA 693 ag232 && chLam.O.all (validA 693) &&
    chSig.O.all (validA 693) && chA1.O.all (validA 693) && chX1.O.all (validA 693) &&
    nativeA.all fun a => validA 693 a && siftA 693 lvA2 chA2.B 0 a

end CFSG.EvenSmallLie.UnitarySix.YamadaSec3
