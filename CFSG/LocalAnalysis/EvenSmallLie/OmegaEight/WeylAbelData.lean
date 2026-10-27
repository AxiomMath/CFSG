module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.WeylAbelPData
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.WeylTData
public import CFSG.RankThree.Native.PermEnumeration

public section

namespace CFSG.EvenSmallLie.OmegaEight.Weyl

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.RankThree.Native
open CFSG.Monster.B.Fischer

@[expose] def perm8Arr (σ : Equiv.Perm (Fin 8)) : Array ℕ := Array.ofFn (n := 8) fun i => (σ i : ℕ)

@[expose] def q1Gens : List (Equiv.Perm (Fin 8)) :=
  [Equiv.swap 0 1, Equiv.swap 2 3, Equiv.swap 4 5, Equiv.swap 6 7]

@[expose] def q0Gens : List (Equiv.Perm (Fin 8)) :=
  [Equiv.swap 0 1 * Equiv.swap 2 3, Equiv.swap 0 1 * Equiv.swap 4 5,
    Equiv.swap 0 1 * Equiv.swap 6 7]

@[expose] def pListArr (i : ℕ) : Array ℕ :=
  Array.ofFn (n := 8) fun j => pCodes / 2 ^ (24 * i) % 2 ^ 24 / 8 ^ j.val % 8

@[expose] def pMul (i j : ℕ) : ℕ := pMulT / 2 ^ (7 * (128 * i + j)) % 128

@[expose] def pInv (i : ℕ) : ℕ := pInvT / 2 ^ (7 * i) % 128

@[expose] def pPar (i : ℕ) : ℕ := pParT / 2 ^ (7 * i) % 128

@[expose] def pLab (i : ℕ) : ℕ := pLabT / 2 ^ (3 * i) % 8

@[expose] def wordIdx (gi w : List ℕ) : ℕ := w.foldr (fun k acc => pMul (gi.getD k 0) acc) 0

structure PListFacts : Prop where
  valid : ∀ i < 128, validA 8 (pListArr i) = true
  distinct : ∀ i < 128, ∀ j < 128, i ≠ j → eqA 8 (pListArr i) (pListArr j) = false
  id0 : eqA 8 (pListArr 0) (idA 8) = true
  mul : ∀ i < 128, ∀ j < 128,
    eqA 8 (compA 8 (pListArr i) (pListArr j)) (pListArr (pMul i j)) = true
  inv : ∀ i < 128, eqA 8 (compA 8 (pListArr i) (pListArr (pInv i))) (idA 8) = true
  gens : ∀ k < 7,
    eqA 8 (perm8Arr ((Equiv.swap 0 1 :: pPlusGens).getD k 1)) (pListArr (k + 1)) = true
  tree : ∀ i < 128, 0 < i → pPar i < i ∧ pLab i < 7 ∧ pMul (pLab i + 1) (pPar i) = i

structure SubListFacts (gs : List (Equiv.Perm (Fin 8))) (gi : List ℕ) (M : ℕ)
    (W : List (List ℕ)) : Prop where
  len : gi.length = gs.length
  gens : ∀ k < gs.length, eqA 8 (perm8Arr (gs.getD k 1)) (pListArr (gi.getD k 0)) = true
  idx : ∀ k < gi.length, gi.getD k 0 < 128 ∧ M.testBit (gi.getD k 0) = true
  one : M.testBit 0 = true
  lt : M < 2 ^ 128
  mul : ∀ i < 128, ∀ j < 128, M.testBit i = true → M.testBit j = true → M.testBit (pMul i j) = true
  inv : ∀ i < 128, M.testBit i = true → M.testBit (pInv i) = true
  words : ∀ i < 128, M.testBit i = true → ∃ w ∈ W, wordIdx gi w = i

@[expose] def bitsOf (p : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | n + 1 => bitsOf p n ||| (if p n then 2 ^ n else 0)

@[expose] def extMask (m x : ℕ) : ℕ :=
  m ||| bitsOf (fun j => m.testBit (pMul (pInv x) j)) 128

@[expose] def validExt (m x : ℕ) : Bool :=
  !m.testBit x && m.testBit (pMul x x) &&
    (List.range 128).all fun i => !m.testBit i || pMul x i == pMul i x

@[expose] def layer (k : ℕ) : List ℕ := layerLists.getD k []

@[expose] def fixA (a : Array ℕ) (n : ℕ) : Bool :=
  (List.range 8).all fun j => n.testBit a[j]! == n.testBit j

@[expose] def fixEven (m : ℕ) : ℕ :=
  ((List.range 256).filter fun n => framePop n % 2 == 0 &&
    (List.range 128).all fun i => !m.testBit i || fixA (pListArr i) n).length

@[expose] def subMask (m m' : ℕ) : Bool :=
  (List.range 128).all fun i => !m.testBit i || m'.testBit i

@[expose] def layerValOK (k m : ℕ) : Bool :=
  decide (fixEven m * 2 ^ k ≤ 256) && (fixEven m * 2 ^ k != 256 || m == q1Mask) &&
    (!subMask m pPlusMask || (decide (fixEven m * 2 ^ k ≤ 128) &&
      (fixEven m * 2 ^ k != 128 || m == 1 || m == q0Mask)))

structure LayerFacts : Prop where
  closed : ∀ k < 5, ∀ m ∈ layer k, ∀ x < 128, validExt m x = true → extMask m x ∈ layer (k + 1)
  val : ∀ k < 5, ∀ m ∈ layer k, layerValOK k m = true

@[expose] def liftReps : List ℕ := [0, 10, 34, 40, 130, 136, 160, 170]

@[expose] def liftArr (r : ℕ) (σ : Equiv.Perm (Fin 8)) : Array ℕ :=
  compA 240 signArrs[r]! (permArr σ)

@[expose] def uPrimeGensArr : Array (Array ℕ) :=
  #[signArr (vec2 0 1), compA 240 (signArr (vec2 0 2)) (permArr (Equiv.swap 0 1 * Equiv.swap 2 3)),
    compA 240 (signArr (vec2 0 4)) (permArr (Equiv.swap 0 1 * Equiv.swap 4 5)),
    compA 240 (signArr (vec2 0 6)) (permArr (Equiv.swap 0 1 * Equiv.swap 6 7))]

@[expose] def uMasks : List ℕ :=
  [0, 3, 5, 17, 65, 6, 18, 66, 15, 23, 71, 51, 83, 195, 12, 20, 68, 48, 80, 192, 10, 30, 78, 54,
    86, 198, 34, 114, 210, 130, 9, 29, 77, 53, 85, 197, 33, 113, 209, 129, 24, 72, 60, 92, 204,
    36, 116, 212, 132, 96, 240, 144, 27, 75, 63, 95, 207, 39, 119, 215, 135, 99, 243, 147, 57, 89,
    201, 45, 125, 221, 141, 101, 245, 149, 225, 177, 58, 90, 202, 46, 126, 222, 142, 102, 246,
    150, 226, 178, 43, 123, 219, 139, 111, 255, 159, 231, 183, 163, 40, 120, 216, 136, 108, 252,
    156, 228, 180, 160, 106, 250, 154, 238, 190, 166, 105, 249, 153, 237, 189, 165, 232, 184, 172,
    235, 187, 175, 169, 170]

@[expose] def uPerms : List (List ℕ) :=
  [[0, 1, 2, 3, 4, 5, 6, 7], [0, 1, 2, 3, 4, 5, 6, 7], [1, 0, 3, 2, 4, 5, 6, 7],
    [1, 0, 2, 3, 5, 4, 6, 7], [1, 0, 2, 3, 4, 5, 7, 6], [1, 0, 3, 2, 4, 5, 6, 7],
    [1, 0, 2, 3, 5, 4, 6, 7], [1, 0, 2, 3, 4, 5, 7, 6], [0, 1, 2, 3, 4, 5, 6, 7],
    [0, 1, 3, 2, 5, 4, 6, 7], [0, 1, 3, 2, 4, 5, 7, 6], [0, 1, 2, 3, 4, 5, 6, 7],
    [0, 1, 2, 3, 5, 4, 7, 6], [0, 1, 2, 3, 4, 5, 6, 7], [0, 1, 2, 3, 4, 5, 6, 7],
    [0, 1, 3, 2, 5, 4, 6, 7], [0, 1, 3, 2, 4, 5, 7, 6], [0, 1, 2, 3, 4, 5, 6, 7],
    [0, 1, 2, 3, 5, 4, 7, 6], [0, 1, 2, 3, 4, 5, 6, 7], [1, 0, 3, 2, 4, 5, 6, 7],
    [1, 0, 2, 3, 5, 4, 6, 7], [1, 0, 2, 3, 4, 5, 7, 6], [1, 0, 3, 2, 4, 5, 6, 7],
    [1, 0, 3, 2, 5, 4, 7, 6], [1, 0, 3, 2, 4, 5, 6, 7], [1, 0, 2, 3, 5, 4, 6, 7],
    [1, 0, 2, 3, 4, 5, 7, 6], [1, 0, 2, 3, 5, 4, 6, 7], [1, 0, 2, 3, 4, 5, 7, 6],
    [1, 0, 3, 2, 4, 5, 6, 7], [1, 0, 2, 3, 5, 4, 6, 7], [1, 0, 2, 3, 4, 5, 7, 6],
    [1, 0, 3, 2, 4, 5, 6, 7], [1, 0, 3, 2, 5, 4, 7, 6], [1, 0, 3, 2, 4, 5, 6, 7],
    [1, 0, 2, 3, 5, 4, 6, 7], [1, 0, 2, 3, 4, 5, 7, 6], [1, 0, 2, 3, 5, 4, 6, 7],
    [1, 0, 2, 3, 4, 5, 7, 6], [0, 1, 3, 2, 5, 4, 6, 7], [0, 1, 3, 2, 4, 5, 7, 6],
    [0, 1, 2, 3, 4, 5, 6, 7], [0, 1, 2, 3, 5, 4, 7, 6], [0, 1, 2, 3, 4, 5, 6, 7],
    [0, 1, 3, 2, 5, 4, 6, 7], [0, 1, 3, 2, 4, 5, 7, 6], [0, 1, 3, 2, 5, 4, 6, 7],
    [0, 1, 3, 2, 4, 5, 7, 6], [0, 1, 2, 3, 5, 4, 7, 6], [0, 1, 2, 3, 4, 5, 6, 7],
    [0, 1, 2, 3, 5, 4, 7, 6], [0, 1, 3, 2, 5, 4, 6, 7], [0, 1, 3, 2, 4, 5, 7, 6],
    [0, 1, 2, 3, 4, 5, 6, 7], [0, 1, 2, 3, 5, 4, 7, 6], [0, 1, 2, 3, 4, 5, 6, 7],
    [0, 1, 3, 2, 5, 4, 6, 7], [0, 1, 3, 2, 4, 5, 7, 6], [0, 1, 3, 2, 5, 4, 6, 7],
    [0, 1, 3, 2, 4, 5, 7, 6], [0, 1, 2, 3, 5, 4, 7, 6], [0, 1, 2, 3, 4, 5, 6, 7],
    [0, 1, 2, 3, 5, 4, 7, 6], [1, 0, 3, 2, 4, 5, 6, 7], [1, 0, 3, 2, 5, 4, 7, 6],
    [1, 0, 3, 2, 4, 5, 6, 7], [1, 0, 2, 3, 5, 4, 6, 7], [1, 0, 2, 3, 4, 5, 7, 6],
    [1, 0, 2, 3, 5, 4, 6, 7], [1, 0, 2, 3, 4, 5, 7, 6], [1, 0, 3, 2, 5, 4, 7, 6],
    [1, 0, 3, 2, 4, 5, 6, 7], [1, 0, 3, 2, 5, 4, 7, 6], [1, 0, 2, 3, 5, 4, 6, 7],
    [1, 0, 2, 3, 4, 5, 7, 6], [1, 0, 3, 2, 4, 5, 6, 7], [1, 0, 3, 2, 5, 4, 7, 6],
    [1, 0, 3, 2, 4, 5, 6, 7], [1, 0, 2, 3, 5, 4, 6, 7], [1, 0, 2, 3, 4, 5, 7, 6],
    [1, 0, 2, 3, 5, 4, 6, 7], [1, 0, 2, 3, 4, 5, 7, 6], [1, 0, 3, 2, 5, 4, 7, 6],
    [1, 0, 3, 2, 4, 5, 6, 7], [1, 0, 3, 2, 5, 4, 7, 6], [1, 0, 2, 3, 5, 4, 6, 7],
    [1, 0, 2, 3, 4, 5, 7, 6], [0, 1, 3, 2, 5, 4, 6, 7], [0, 1, 3, 2, 4, 5, 7, 6],
    [0, 1, 3, 2, 5, 4, 6, 7], [0, 1, 3, 2, 4, 5, 7, 6], [0, 1, 2, 3, 5, 4, 7, 6],
    [0, 1, 2, 3, 4, 5, 6, 7], [0, 1, 2, 3, 5, 4, 7, 6], [0, 1, 3, 2, 5, 4, 6, 7],
    [0, 1, 3, 2, 4, 5, 7, 6], [0, 1, 2, 3, 5, 4, 7, 6], [0, 1, 3, 2, 5, 4, 6, 7],
    [0, 1, 3, 2, 4, 5, 7, 6], [0, 1, 3, 2, 5, 4, 6, 7], [0, 1, 3, 2, 4, 5, 7, 6],
    [0, 1, 2, 3, 5, 4, 7, 6], [0, 1, 2, 3, 4, 5, 6, 7], [0, 1, 2, 3, 5, 4, 7, 6],
    [0, 1, 3, 2, 5, 4, 6, 7], [0, 1, 3, 2, 4, 5, 7, 6], [0, 1, 2, 3, 5, 4, 7, 6],
    [1, 0, 3, 2, 5, 4, 7, 6], [1, 0, 3, 2, 4, 5, 6, 7], [1, 0, 3, 2, 5, 4, 7, 6],
    [1, 0, 2, 3, 5, 4, 6, 7], [1, 0, 2, 3, 4, 5, 7, 6], [1, 0, 3, 2, 5, 4, 7, 6],
    [1, 0, 3, 2, 5, 4, 7, 6], [1, 0, 3, 2, 4, 5, 6, 7], [1, 0, 3, 2, 5, 4, 7, 6],
    [1, 0, 2, 3, 5, 4, 6, 7], [1, 0, 2, 3, 4, 5, 7, 6], [1, 0, 3, 2, 5, 4, 7, 6],
    [0, 1, 3, 2, 5, 4, 6, 7], [0, 1, 3, 2, 4, 5, 7, 6], [0, 1, 2, 3, 5, 4, 7, 6],
    [0, 1, 3, 2, 5, 4, 6, 7], [0, 1, 3, 2, 4, 5, 7, 6], [0, 1, 2, 3, 5, 4, 7, 6],
    [1, 0, 3, 2, 5, 4, 7, 6], [1, 0, 3, 2, 5, 4, 7, 6]]

@[expose] def uPrimeCert : ArrCert :=
  ⟨Array.ofFn (n := 128) fun i => spArr (uMasks.getD i.val 0) (uPerms.getD i.val []), #[], #[], #[]⟩

@[expose] def memU (x : Array ℕ) : Bool := uPrimeCert.pts.toList.any (eqA 240 x)

@[expose] def lift1Check : Bool :=
  liftReps.all fun r0 => liftReps.all fun r1 => liftReps.all fun r2 => liftReps.all fun r3 =>
    let x0 := liftArr r0 (Equiv.swap 0 1)
    let x1 := liftArr r1 (Equiv.swap 2 3)
    let x2 := liftArr r2 (Equiv.swap 4 5)
    let x3 := liftArr r3 (Equiv.swap 6 7)
    !(commA' x0 x1 && commA' x0 x2 && commA' x0 x3 && commA' x1 x2 && commA' x1 x3 &&
      commA' x2 x3) ||
      (memE1 frameArrs x0 && memE1 frameArrs x1 && memE1 frameArrs x2 && memE1 frameArrs x3)

@[expose] def lift0Check : Bool :=
  liftReps.all fun r0 => liftReps.all fun r1 => liftReps.all fun r2 =>
    let x0 := liftArr r0 (Equiv.swap 0 1 * Equiv.swap 2 3)
    let x1 := liftArr r1 (Equiv.swap 0 1 * Equiv.swap 4 5)
    let x2 := liftArr r2 (Equiv.swap 0 1 * Equiv.swap 6 7)
    !(commA' x0 x1 && commA' x0 x2 && commA' x1 x2) ||
      (memE1 frameArrs x0 && memE1 frameArrs x1 && memE1 frameArrs x2) ||
      (memU x0 && memU x1 && memU x2)

structure UListFacts : Prop where
  valid : ∀ i < 128, isInvA 240 uPrimeCert.pts[i]! (invCand 240 uPrimeCert.pts[i]!) = true
  distinct : ∀ i < 128, ∀ j < 128, i ≠ j →
    eqA 240 uPrimeCert.pts[i]! uPrimeCert.pts[j]! = false
  id0 : isId uPrimeCert.pts[0]! = true
  gens : ∀ k < 4, isInvA 240 uPrimeGensArr[k]! (invCand 240 uPrimeGensArr[k]!) = true
  tree : ∀ i < 128, 0 < i → ∃ k < 4, ∃ j < i,
    eqA 240 uPrimeCert.pts[i]! (compA 240 uPrimeGensArr[k]! uPrimeCert.pts[j]!) = true
  closed : ∀ i < 128, ∀ k < 4, ∃ j < 128,
    eqA 240 (compA 240 uPrimeGensArr[k]! uPrimeCert.pts[i]!) uPrimeCert.pts[j]! = true
  closedInv : ∀ i < 128, ∀ k < 4, ∃ j < 128,
    eqA 240 (compA 240 (invCand 240 uPrimeGensArr[k]!) uPrimeCert.pts[i]!) uPrimeCert.pts[j]! =
      true
  comm : ∀ i < 4, ∀ j < 4, commA' uPrimeGensArr[i]! uPrimeGensArr[j]! = true
  sq : isId (compA 240 uPrimeGensArr[1]! uPrimeGensArr[1]!) = false

end CFSG.EvenSmallLie.OmegaEight.Weyl
