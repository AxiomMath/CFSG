module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.WeylBridgeData
public import CFSG.Monster.B.Fischer.ArrCert
public import CFSG.RankThree.Native.DerivedGenerators

public section

namespace CFSG.EvenSmallLie.OmegaEight.Weyl

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.RankThree.Native
open CFSG.Monster.B.Fischer

@[expose] def keyPts : List ℕ := [1, 0, 53, 52, 89, 88, 109, 108]

@[expose] def tPlusGensArr : Array (Array ℕ) :=
  ((List.range 7).map (fun i => signArr (frameDecode (1 + 2 ^ (i + 1)))) ++
    pPlusGens.map permArr).toArray

@[expose] def s0Arr : Array ℕ := reflArr 1


@[expose] def isId (x : Array ℕ) : Bool := eqA 240 x (idA 240)

@[expose] def commA' (x g : Array ℕ) : Bool := eqA 240 (compA 240 x g) (compA 240 g x)

@[expose] def conjA' (g x : Array ℕ) : Array ℕ := compA 240 (compA 240 g x) (invCand 240 g)

@[expose] def pairMasks : List ℕ :=
  (List.range 8).flatMap fun a => ((List.range 8).filter (a < ·)).map fun b => 2 ^ a + 2 ^ b

@[expose] def signArrs : Array (Array ℕ) :=
  ((List.range 256).map fun m => signArr (frameDecode m)).toArray

@[expose] def frameArrs : Array (Array ℕ) :=
  ((List.range 256).map fun m => frameArr (frameDecode m)).toArray

@[expose] def fgOK (SA : Array (Array ℕ)) (t : Array ℕ) : Bool :=
  pairMasks.any fun m =>
    let s := SA[m]!
    let c := compA 240 (compA 240 s t) (compA 240 s t)
    !isId c && !(eqA 240 c negArr) && isId (compA 240 c c)

@[expose] def listPermVec (l : List ℕ) (x : List ℤ) : List ℤ :=
  (List.range 8).map fun j => x.getD (l.idxOf j) 0

@[expose] def listPermArr (l : List ℕ) : Array ℕ :=
  Array.ofFn (n := 240) fun i => rootIdx (listPermVec l (rootVec i.val))
@[expose] def rhoLists : List (List ℕ) :=
  [[4, 5, 0, 1, 6, 7, 2, 3], [0, 1, 6, 7, 2, 4, 5, 3], [0, 1, 6, 7, 2, 4, 3, 5],
    [0, 2, 3, 1, 4, 5, 6, 7], [0, 2, 1, 3, 4, 5, 6, 7], [0, 2, 1, 3, 6, 4, 7, 5],
    [0, 2, 3, 1, 4, 6, 7, 5], [4, 6, 7, 5, 0, 2, 1, 3], [0, 2, 1, 3, 4, 6, 7, 5],
    [0, 1, 2, 6, 7, 3, 4, 5], [2, 3, 0, 4, 1, 5, 6, 7], [6, 4, 0, 1, 7, 5, 2, 3],
    [6, 2, 0, 1, 3, 7, 4, 5], [0, 1, 6, 4, 2, 3, 7, 5], [4, 6, 0, 1, 2, 3, 5, 7],
    [0, 1, 6, 4, 2, 3, 5, 7], [4, 6, 0, 1, 2, 3, 7, 5], [0, 2, 4, 6, 1, 3, 7, 5],
    [0, 2, 4, 6, 1, 3, 5, 7], [0, 2, 4, 6, 5, 7, 3, 1], [0, 2, 4, 6, 3, 1, 5, 7],
    [0, 2, 4, 6, 7, 5, 1, 3], [0, 2, 4, 6, 7, 5, 3, 1], [0, 2, 4, 6, 3, 1, 7, 5],
    [0, 2, 4, 6, 5, 7, 1, 3]]

@[expose] def rhoArrs : Array (Array ℕ) := (rhoLists.map listPermArr).toArray

@[expose] def pPlusImgs : List (List ℕ) :=
  [[0, 1, 2, 3, 4, 5, 6, 7], [1, 0, 3, 2, 4, 5, 6, 7], [2, 3, 0, 1, 4, 5, 6, 7],
    [0, 1, 2, 3, 5, 4, 7, 6], [0, 1, 2, 3, 6, 7, 4, 5], [1, 0, 2, 3, 5, 4, 6, 7],
    [4, 5, 6, 7, 0, 1, 2, 3], [3, 2, 1, 0, 4, 5, 6, 7], [1, 0, 3, 2, 5, 4, 7, 6],
    [1, 0, 3, 2, 6, 7, 4, 5], [0, 1, 3, 2, 5, 4, 6, 7], [5, 4, 7, 6, 0, 1, 2, 3],
    [2, 3, 0, 1, 5, 4, 7, 6], [2, 3, 0, 1, 6, 7, 4, 5], [2, 3, 1, 0, 5, 4, 6, 7],
    [6, 7, 4, 5, 0, 1, 2, 3], [0, 1, 2, 3, 7, 6, 5, 4], [1, 0, 2, 3, 4, 5, 7, 6],
    [4, 5, 6, 7, 1, 0, 3, 2], [1, 0, 2, 3, 6, 7, 5, 4], [4, 5, 6, 7, 2, 3, 0, 1],
    [3, 2, 0, 1, 5, 4, 6, 7], [1, 0, 2, 3, 7, 6, 4, 5], [5, 4, 6, 7, 1, 0, 2, 3],
    [3, 2, 1, 0, 5, 4, 7, 6], [3, 2, 1, 0, 6, 7, 4, 5], [7, 6, 5, 4, 0, 1, 2, 3],
    [1, 0, 3, 2, 7, 6, 5, 4], [0, 1, 3, 2, 4, 5, 7, 6], [5, 4, 7, 6, 1, 0, 3, 2],
    [0, 1, 3, 2, 6, 7, 5, 4], [5, 4, 7, 6, 2, 3, 0, 1], [0, 1, 3, 2, 7, 6, 4, 5],
    [4, 5, 7, 6, 1, 0, 2, 3], [2, 3, 0, 1, 7, 6, 5, 4], [2, 3, 1, 0, 4, 5, 7, 6],
    [6, 7, 4, 5, 1, 0, 3, 2], [2, 3, 1, 0, 6, 7, 5, 4], [6, 7, 4, 5, 2, 3, 0, 1],
    [2, 3, 1, 0, 7, 6, 4, 5], [6, 7, 5, 4, 1, 0, 2, 3], [4, 5, 6, 7, 3, 2, 1, 0],
    [3, 2, 0, 1, 4, 5, 7, 6], [5, 4, 6, 7, 0, 1, 3, 2], [3, 2, 0, 1, 6, 7, 5, 4],
    [5, 4, 6, 7, 2, 3, 1, 0], [3, 2, 0, 1, 7, 6, 4, 5], [7, 6, 4, 5, 1, 0, 2, 3],
    [5, 4, 6, 7, 3, 2, 0, 1], [3, 2, 1, 0, 7, 6, 5, 4], [7, 6, 5, 4, 1, 0, 3, 2],
    [7, 6, 5, 4, 2, 3, 0, 1], [5, 4, 7, 6, 3, 2, 1, 0], [4, 5, 7, 6, 0, 1, 3, 2],
    [4, 5, 7, 6, 2, 3, 1, 0], [4, 5, 7, 6, 3, 2, 0, 1], [6, 7, 4, 5, 3, 2, 1, 0],
    [6, 7, 5, 4, 0, 1, 3, 2], [6, 7, 5, 4, 2, 3, 1, 0], [6, 7, 5, 4, 3, 2, 0, 1],
    [7, 6, 4, 5, 0, 1, 3, 2], [7, 6, 4, 5, 2, 3, 1, 0], [7, 6, 4, 5, 3, 2, 0, 1],
    [7, 6, 5, 4, 3, 2, 1, 0]]

@[expose] def evenMask (r : ℕ) : ℕ := 2 * r + framePop r % 2

@[expose] def spArr (m : ℕ) (l : List ℕ) : Array ℕ := compA 240 signArrs[m]! (listPermArr l)

@[expose] def tPlusCert : ArrCert :=
  ⟨Array.ofFn (n := 8192) fun i => spArr (evenMask (i.val % 128)) (pPlusImgs.getD (i.val / 128) []),
    #[], #[], #[]⟩

@[expose] def frameMaskOf (x : Array ℕ) : ℕ :=
  ((List.range 8).filter fun i => x[keyPts.getD i 0]! == negArr[keyPts.getD i 0]!).foldl
    (fun m i => m + 2 ^ i) 0 % 256

@[expose] def memE1 (FA : Array (Array ℕ)) (x : Array ℕ) : Bool := eqA 240 x FA[frameMaskOf x]!

@[expose] def w8OK (FA RA : Array (Array ℕ)) (x : Array ℕ) : Bool :=
  (List.range 25).any fun k => memE1 FA (conjA' RA[k]! x)

@[expose] def tElt (c : ArrCert) (i : ℕ) (b : Bool) : Array ℕ :=
  if b then compA 240 c.pts[i]! s0Arr else c.pts[i]!

structure TListFacts : Prop where
  valid : ∀ i < 8192, isInvA 240 (tElt tPlusCert i false) (invCand 240 (tElt tPlusCert i false)) =
    true
  distinct : ∀ i < 8192, ∀ j < 8192, i ≠ j →
    eqA 240 (tElt tPlusCert i false) (tElt tPlusCert j false) = false
  id0 : isId (tElt tPlusCert 0 false) = true
  gens : ∀ k < 13, isInvA 240 tPlusGensArr[k]! (invCand 240 tPlusGensArr[k]!) = true ∧
    isId (compA 240 tPlusGensArr[k]! tPlusGensArr[k]!) = true
  tree : ∀ i < 8192, 0 < i → ∃ k < 13, ∃ j < i,
    eqA 240 (tElt tPlusCert i false) (compA 240 tPlusGensArr[k]! (tElt tPlusCert j false)) = true
  closed : ∀ i < 8192, ∀ k < 13, ∃ j < 8192,
    eqA 240 (compA 240 tPlusGensArr[k]! (tElt tPlusCert i false)) (tElt tPlusCert j false) = true
  sign : ∀ m < 256, framePop m % 2 = 0 → ∃ i < 8192,
    eqA 240 signArrs[m]! (tElt tPlusCert i false) = true
  s0 : ∀ k < 13, ∃ j < 8192,
    eqA 240 (compA 240 (compA 240 s0Arr tPlusGensArr[k]!) s0Arr) (tElt tPlusCert j false) = true
  sqz : ∀ i < 8192, eqA 240 (compA 240 (tElt tPlusCert i true) (tElt tPlusCert i true)) negArr =
    false
  fg : ∀ i < 8192, isId (compA 240 (tElt tPlusCert i true) (tElt tPlusCert i true)) = true →
    fgOK signArrs (tElt tPlusCert i true) = true
  w8 : ∀ i < 8192, ∀ b ∈ [false, true],
    isId (compA 240 (tElt tPlusCert i b) (tElt tPlusCert i b)) = true →
      isId (tElt tPlusCert i b) = true ∨ w8OK frameArrs rhoArrs (tElt tPlusCert i b) = true
  cent : ∀ i < 8192, ∀ b ∈ [false, true],
    (allLt 13 (fun k => commA' (tElt tPlusCert i b) tPlusGensArr[k]!) = true ∧
      commA' (tElt tPlusCert i b) s0Arr = true) →
      isId (tElt tPlusCert i b) = true ∨ eqA 240 (tElt tPlusCert i b) negArr = true
  centPlus : ∀ i < 8192,
    allLt 13 (fun k => commA' (tElt tPlusCert i false) tPlusGensArr[k]!) = true →
      isId (tElt tPlusCert i false) = true ∨ eqA 240 (tElt tPlusCert i false) negArr = true

@[expose] def rhoWords : List (List ℕ) :=
  [[13, 41, 57, 77, 93, 105], [65, 85, 93, 101], [65, 85, 93, 101, 109], [29, 53], [29],
    [29, 93, 101, 109], [29, 53, 101, 109], [13, 45, 69, 77, 105], [29, 101, 109],
    [81, 97, 101, 109], [5, 33, 73], [21, 37, 65, 73, 97], [21, 29, 65, 81, 93, 105],
    [65, 73, 93, 101, 109], [13, 45, 57, 81, 101], [65, 73, 93, 101], [13, 45, 57, 81, 101, 109],
    [29, 57, 81, 101, 109], [29, 57, 81, 101], [29, 57, 81, 89, 105], [29, 57, 81, 93, 101],
    [29, 57, 81, 97, 109], [29, 57, 81, 97], [29, 57, 81, 93, 101, 109],
    [29, 57, 81, 89, 105, 109]]

@[expose] def rhoWordCheck : Bool :=
  allLt 25 fun k => isInvA 240 rhoArrs[k]! (invCand 240 rhoArrs[k]!) &&
    eqA 240 rhoArrs[k]! (wordArr (rhoWords.getD k []))

@[expose] def tGenWords : List (List ℕ) :=
  [[1, 0], [5, 4], [9, 8], [13, 12], [17, 16], [21, 20], [25, 24], [1, 53], [5, 33], [89, 109],
    [93, 105], [1, 89], [13, 41, 65, 85]]

@[expose] def tGenCheck : Bool :=
  allLt 13 fun k => eqA 240 tPlusGensArr[k]! (wordArr (tGenWords.getD k []))

end CFSG.EvenSmallLie.OmegaEight.Weyl
