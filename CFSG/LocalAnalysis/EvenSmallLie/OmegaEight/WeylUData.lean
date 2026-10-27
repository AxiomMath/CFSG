module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.WeylTData

public section

namespace CFSG.EvenSmallLie.OmegaEight.Weyl

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.RankThree.Native
open CFSG.Monster.B.Fischer

@[expose] def cGens : List (Equiv.Perm (Fin 8)) :=
  [Equiv.swap 0 1, Equiv.swap 0 1 * Equiv.swap 2 3, Equiv.swap 0 2 * Equiv.swap 1 3,
    Equiv.swap 4 5 * Equiv.swap 6 7, Equiv.swap 4 6 * Equiv.swap 5 7,
    Equiv.swap 0 1 * Equiv.swap 4 5]

@[expose] def cWords : List (List ℕ) :=
  [[], [0], [1], [2], [3], [4], [5], [1, 0], [2, 0], [3, 0], [4, 0], [5, 0], [2, 1], [3, 1], [4,
    1], [5, 1], [0, 2], [3, 2], [4, 2], [5, 2], [4, 3], [5, 3], [5, 4], [2, 5], [4, 5], [3, 1, 0],
    [4, 1, 0], [5, 1, 0], [3, 2, 0], [4, 2, 0], [5, 2, 0], [4, 3, 0], [5, 3, 0], [5, 4, 0], [2, 5,
    0], [4, 5, 0], [3, 2, 1], [4, 2, 1], [4, 3, 1], [5, 3, 1], [5, 4, 1], [4, 5, 1], [3, 0, 2], [4,
    0, 2], [4, 3, 2], [5, 3, 2], [5, 4, 2], [4, 5, 2], [2, 5, 3], [2, 5, 4], [4, 2, 5], [4, 3, 1,
    0], [5, 3, 1, 0], [5, 4, 1, 0], [4, 5, 1, 0], [4, 3, 2, 0], [5, 3, 2, 0], [5, 4, 2, 0], [4, 5,
    2, 0], [2, 5, 3, 0], [2, 5, 4, 0], [4, 2, 5, 0], [4, 3, 2, 1], [4, 3, 0, 2]]

@[expose] def cList : List (Equiv.Perm (Fin 8)) :=
  cWords.map fun w => (w.map fun k => cGens.getD k 1).prod

@[expose] def cTab : List (List ℕ) :=
  [[1, 2, 3, 4, 5, 6], [0, 7, 8, 9, 10, 11], [7, 0, 12, 13, 14, 15], [16, 12, 0, 17, 18, 19], [9,
    13, 17, 0, 20, 21], [10, 14, 18, 20, 0, 22], [11, 15, 23, 21, 24, 0], [2, 1, 16, 25, 26, 27],
    [12, 16, 1, 28, 29, 30], [4, 25, 28, 1, 31, 32], [5, 26, 29, 31, 1, 33], [6, 27, 34, 32, 35, 1],
    [8, 3, 2, 36, 37, 23], [25, 4, 36, 2, 38, 39], [26, 5, 37, 38, 2, 40], [27, 6, 19, 39, 41, 2],
    [3, 8, 7, 42, 43, 34], [42, 36, 4, 3, 44, 45], [43, 37, 5, 44, 3, 46], [34, 23, 15, 45, 47, 3],
    [31, 38, 44, 5, 4, 24], [32, 39, 48, 6, 22, 4], [33, 40, 49, 24, 21, 5], [30, 19, 6, 48, 50,
    12], [35, 41, 50, 22, 6, 20], [13, 9, 42, 7, 51, 52], [14, 10, 43, 51, 7, 53], [15, 11, 30, 52,
    54, 7], [36, 42, 9, 8, 55, 56], [37, 43, 10, 55, 8, 57], [23, 34, 27, 56, 58, 8], [20, 51, 55,
    10, 9, 35], [21, 52, 59, 11, 33, 9], [22, 53, 60, 35, 32, 10], [19, 30, 11, 59, 61, 16], [24,
    54, 61, 33, 11, 31], [28, 17, 13, 12, 62, 48], [29, 18, 14, 62, 12, 49], [51, 20, 62, 14, 13,
    41], [52, 21, 45, 15, 40, 13], [53, 22, 46, 41, 39, 14], [54, 24, 47, 40, 15, 38], [17, 28, 25,
    16, 63, 59], [18, 29, 26, 63, 16, 60], [63, 62, 20, 18, 17, 47], [59, 48, 39, 19, 46, 17], [60,
    49, 40, 47, 45, 18], [61, 50, 41, 46, 19, 44], [56, 45, 21, 23, 49, 36], [57, 46, 22, 50, 48,
    37], [58, 47, 24, 49, 23, 62], [38, 31, 63, 26, 25, 54], [39, 32, 56, 27, 53, 25], [40, 33, 57,
    54, 52, 26], [41, 35, 58, 53, 27, 51], [62, 63, 31, 29, 28, 58], [48, 59, 52, 30, 57, 28], [49,
    60, 53, 58, 56, 29], [50, 61, 54, 57, 30, 55], [45, 56, 32, 34, 60, 42], [46, 57, 33, 61, 59,
    43], [47, 58, 35, 60, 34, 63], [55, 44, 38, 37, 36, 50], [44, 55, 51, 43, 42, 61]]

@[expose] def commInv (t ti d : Array ℕ) : Array ℕ := compA 240 (compA 240 (compA 240 t d) ti) d

@[expose] def tInv (c : ArrCert) (i : ℕ) (b : Bool) : Array ℕ :=
  if b then compA 240 s0Arr (invCand 240 c.pts[i]!) else invCand 240 c.pts[i]!

@[expose] def conjStable (t : Array ℕ) : Bool :=
  allLt 13 (fun k => let c := conjA' tPlusGensArr[k]! t
    eqA 240 c t || eqA 240 c (compA 240 t negArr)) &&
    (let c := compA 240 (compA 240 s0Arr t) s0Arr
     eqA 240 c t || eqA 240 c (compA 240 t negArr))

@[expose] def uniqueCheck : Bool :=
  let c := tPlusCert
  allLt 8192 fun i => [false, true].all fun b =>
    let t := tElt c i b
    !(isId (compA 240 t t) && !isId t && !eqA 240 t negArr && conjStable t) ||
      eqA 240 t signArrs[15]! || eqA 240 t signArrs[240]!

@[expose] def commGensC (t : Array ℕ) : Bool :=
  commA' t signArrs[15]! && (List.range 256).all (fun v => !(framePop v % 2 == 0) ||
    commA' t signArrs[v]!) && cGens.all fun g => commA' t (permArr g)

@[expose] def centerCCheck : Bool :=
  let c := tPlusCert
  allLt 8192 fun i => [false, true].all fun b =>
    let t := tElt c i b
    !commGensC t || isId t || eqA 240 t signArrs[15]! || eqA 240 t signArrs[240]! ||
      eqA 240 t negArr

@[expose] def commModGens (t ti : Array ℕ) : Bool :=
  commA' t signArrs[15]! && (List.range 256).all (fun v => !(framePop v % 2 == 0) ||
    memE1 frameArrs (commInv t ti signArrs[v]!)) &&
    cGens.all fun g => memE1 frameArrs (commInv t ti (permArr g))

@[expose] def centerModCheck : Bool :=
  let c := tPlusCert
  allLt 8192 fun i => [false, true].all fun b =>
    let t := tElt c i b
    !commModGens t (tInv c i b) || memE1 frameArrs t ||
      memE1 frameArrs (compA 240 t signArrs[5]!) || memE1 frameArrs (compA 240 t signArrs[80]!) ||
      memE1 frameArrs (compA 240 (compA 240 t signArrs[5]!) signArrs[80]!)

@[expose] def commSetOK (s : Array ℕ) (ws : List ℕ) : Bool :=
  (List.range 256).all (fun v => ws.any fun w =>
    eqA 240 (commInv frameArrs[v]! frameArrs[v]! s) signArrs[w]!) &&
    ws.all fun w => (List.range 256).any fun v =>
      eqA 240 (commInv frameArrs[v]! frameArrs[v]! s) signArrs[w]!

@[expose] def pairMasks16 : List ℕ :=
  [0, 3, 12, 15, 48, 51, 60, 63, 192, 195, 204, 207, 240, 243, 252, 255]

@[expose] def commSetCheck : Bool :=
  commSetOK signArrs[5]! [0, 3, 12, 15] && commSetOK signArrs[80]! [0, 48, 192, 240] &&
    commSetOK signArrs[85]! pairMasks16

end CFSG.EvenSmallLie.OmegaEight.Weyl
