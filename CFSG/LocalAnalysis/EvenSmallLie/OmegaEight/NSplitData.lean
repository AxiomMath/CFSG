module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaParLin
public import CFSG.Certificates.CosetTablePresented
public import Certificates.Data.CFSGNative.Schreier.Check
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NSplitBits
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1Data

public section

namespace CFSG.EvenSmallLie.OmegaEight.NSplit

open CFSG.EvenSmallLie.OmegaEight.Stage1 CFSG.EvenSmallLie.UnitarySix.YamadaPar
open CFSG.Certificates.Native CFSG.CosetTable

@[expose] def aCode (i : ℕ) : ℕ := #[1, 2, 32, 17, 6, 8, 4].getD i 0

@[expose] def genCode (ε : Eps) (i v : ℕ) : ℕ :=
  if bfB ε v (aCode i) == qfB ε (aCode i) then v ^^^ aCode i else v

@[expose] def genArr (ε : Eps) (i : ℕ) : Array ℕ := Array.ofFn (n := 64) fun v => genCode ε i v

@[expose] def genArrs (ε : Eps) : Array (Array ℕ) := Array.ofFn (n := 7) fun i => genArr ε i

@[expose] def wordCode (ε : Eps) : List ℕ → ℕ → ℕ
  | [], v => v
  | i :: w, v => genCode ε i (wordCode ε w v)

@[expose] def nsGenCheck (ε : Eps) : Bool :=
  (List.range 7).all fun i => (List.range 64).all fun v =>
    decide (genCode ε i v < 64) && genCode ε i (genCode ε i v) == v &&
      qfB ε (genCode ε i v) == qfB ε v &&
      (List.range 64).all fun w => genCode ε i (v ^^^ w) == genCode ε i v ^^^ genCode ε i w ^^^
        genCode ε i 0

@[expose] def w0Word : List ℕ :=
  [0, 1, 2, 0, 3, 1, 2, 0, 3, 2, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5,
    4, 3, 2, 0, 6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 2, 0, 6, 5, 4, 3, 1, 2, 3, 4, 5, 6]

@[expose] def relWords : List (List ℕ) :=
  [[0, 0], [1, 1], [2, 2], [3, 3], [4, 4], [5, 5], [6, 6],
    [0, 1, 0, 1], [0, 2, 0, 2, 0, 2], [0, 3, 0, 3], [0, 4, 0, 4], [0, 5, 0, 5], [0, 6, 0, 6],
    [1, 2, 1, 2], [1, 3, 1, 3, 1, 3], [1, 4, 1, 4], [1, 5, 1, 5], [1, 6, 1, 6],
    [2, 3, 2, 3, 2, 3], [2, 4, 2, 4], [2, 5, 2, 5], [2, 6, 2, 6],
    [3, 4, 3, 4, 3, 4], [3, 5, 3, 5], [3, 6, 3, 6],
    [4, 5, 4, 5, 4, 5], [4, 6, 4, 6],
    [5, 6, 5, 6, 5, 6], w0Word]

@[expose] def nsRelCheck (ε : Eps) : Bool :=
  relWords.all fun w => (List.range 64).all fun v => wordCode ε w v == v

@[expose] def relPG : List (List (Fin 7 × Bool)) :=
  relWords.map fun w => w.map fun i => (Fin.ofNat 7 i, true)

@[expose] def relE6 : List (List (Fin (subsetOf 7 [0, 1, 2, 3, 4, 5]).length × Bool)) :=
  restrictWords (subsetOf 7 [0, 1, 2, 3, 4, 5]) relPG

@[expose] def relD5 : List (List (Fin (subsetOf 6 [1, 2, 3, 4, 5]).length × Bool)) :=
  restrictWords (subsetOf 6 [1, 2, 3, 4, 5]) relE6

@[expose] def relA4 : List (List (Fin (subsetOf 5 [1, 2, 3, 4]).length × Bool)) :=
  restrictWords (subsetOf 5 [1, 2, 3, 4]) relD5

@[expose] def relA3 : List (List (Fin (subsetOf 4 [0, 1, 2]).length × Bool)) :=
  restrictWords (subsetOf 4 [0, 1, 2]) relA4

@[expose] def relA2 : List (List (Fin (subsetOf 3 [0, 1]).length × Bool)) :=
  restrictWords (subsetOf 3 [0, 1]) relA3

@[expose] def relA1 : List (List (Fin (subsetOf 2 [0]).length × Bool)) :=
  restrictWords (subsetOf 2 [0]) relA2

@[expose] def nsCosetCheck : Bool :=
  subsetCheck relPG [0, 1, 2, 3, 4, 5] 1000 28 && subsetCheck relE6 [1, 2, 3, 4, 5] 1000 27 &&
    subsetCheck relD5 [1, 2, 3, 4] 1000 16 && subsetCheck relA4 [0, 1, 2] 1000 5 &&
    subsetCheck relA3 [0, 1] 1000 4 && subsetCheck relA2 [0] 1000 3 &&
    subsetCheck relA1 [] 1000 2

@[expose] def extraStrongPlus : List (Array ℕ) := [
  #[0, 32, 2, 34, 4, 36, 6, 38, 8, 40, 10, 42, 12, 44, 14, 46, 16, 48, 18, 50, 20, 52, 22, 54,
    24, 56, 26, 58, 28, 60, 30, 62, 1, 33, 3, 35, 5, 37, 7, 39, 9, 41, 11, 43, 13, 45, 15, 47,
    17, 49, 19, 51, 21, 53, 23, 55, 25, 57, 27, 59, 29, 61, 31, 63],
  #[0, 1, 17, 16, 4, 5, 21, 20, 8, 9, 25, 24, 12, 13, 29, 28, 3, 2, 18, 19, 7, 6, 22, 23, 11, 10,
    26, 27, 15, 14, 30, 31, 51, 50, 34, 35, 55, 54, 38, 39, 59, 58, 42, 43, 63, 62, 46, 47, 48,
    49, 33, 32, 52, 53, 37, 36, 56, 57, 41, 40, 60, 61, 45, 44],
  #[0, 1, 2, 3, 4, 5, 6, 7, 10, 11, 8, 9, 14, 15, 12, 13, 20, 21, 22, 23, 16, 17, 18, 19, 30, 31,
    28, 29, 26, 27, 24, 25, 32, 33, 34, 35, 36, 37, 38, 39, 42, 43, 40, 41, 46, 47, 44, 45, 52,
    53, 54, 55, 48, 49, 50, 51, 62, 63, 60, 61, 58, 59, 56, 57],
  #[0, 48, 51, 3, 4, 52, 55, 7, 8, 56, 59, 11, 12, 60, 63, 15, 16, 32, 35, 19, 20, 36, 39, 23,
    24, 40, 43, 27, 28, 44, 47, 31, 17, 33, 34, 18, 21, 37, 38, 22, 25, 41, 42, 26, 29, 45, 46,
    30, 1, 49, 50, 2, 5, 53, 54, 6, 9, 57, 58, 10, 13, 61, 62, 14],
  #[0, 1, 2, 3, 4, 5, 6, 7, 9, 8, 11, 10, 13, 12, 15, 14, 16, 17, 18, 19, 20, 21, 22, 23, 25, 24,
    27, 26, 29, 28, 31, 30, 36, 37, 38, 39, 32, 33, 34, 35, 45, 44, 47, 46, 41, 40, 43, 42, 52,
    53, 54, 55, 48, 49, 50, 51, 61, 60, 63, 62, 57, 56, 59, 58],
  #[0, 1, 2, 3, 10, 11, 8, 9, 6, 7, 4, 5, 12, 13, 14, 15, 30, 31, 28, 29, 20, 21, 22, 23, 24, 25,
    26, 27, 18, 19, 16, 17, 32, 33, 34, 35, 42, 43, 40, 41, 38, 39, 36, 37, 44, 45, 46, 47, 62,
    63, 60, 61, 52, 53, 54, 55, 56, 57, 58, 59, 50, 51, 48, 49],
  #[0, 1, 2, 3, 6, 7, 4, 5, 8, 9, 10, 11, 14, 15, 12, 13, 24, 25, 26, 27, 30, 31, 28, 29, 16, 17,
    18, 19, 22, 23, 20, 21, 32, 33, 34, 35, 38, 39, 36, 37, 40, 41, 42, 43, 46, 47, 44, 45, 56,
    57, 58, 59, 62, 63, 60, 61, 48, 49, 50, 51, 54, 55, 52, 53],
  #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 17, 16, 19, 18, 21, 20, 23, 22, 25, 24,
    27, 26, 29, 28, 31, 30, 34, 35, 32, 33, 38, 39, 36, 37, 42, 43, 40, 41, 46, 47, 44, 45, 51,
    50, 49, 48, 55, 54, 53, 52, 59, 58, 57, 56, 63, 62, 61, 60],
  #[0, 1, 2, 3, 5, 4, 7, 6, 8, 9, 10, 11, 13, 12, 15, 14, 17, 16, 19, 18, 20, 21, 22, 23, 25, 24,
    27, 26, 28, 29, 30, 31, 42, 43, 40, 41, 47, 46, 45, 44, 34, 35, 32, 33, 39, 38, 37, 36, 59,
    58, 57, 56, 62, 63, 60, 61, 51, 50, 49, 48, 54, 55, 52, 53]]
@[expose] def extraWordsPlus : List (List ℤ) := [
  [-1, 3, 1],
  [-2, 4, 2],
  [-7, 5, 2],
  [-3, 4, 3],
  [-8, -9, -11, 10, 11, 9, 8],
  [-5, 6, 5],
  [-13, 10, 13],
  [-14, -12, 14, 12],
  [-13, 12, 13]]
@[expose] def chainBasePlus : List ℕ := [0, 1, 2, 8, 4, 16]

@[expose] def extraStrongMinus : List (Array ℕ) := [
  #[0, 1, 2, 3, 14, 15, 12, 13, 8, 9, 10, 11, 6, 7, 4, 5, 26, 27, 24, 25, 20, 21, 22, 23, 18, 19,
    16, 17, 28, 29, 30, 31, 32, 33, 34, 35, 46, 47, 44, 45, 40, 41, 42, 43, 38, 39, 36, 37, 58,
    59, 56, 57, 52, 53, 54, 55, 50, 51, 48, 49, 60, 61, 62, 63],
  #[0, 32, 2, 34, 4, 36, 6, 38, 8, 40, 10, 42, 12, 44, 14, 46, 16, 48, 18, 50, 20, 52, 22, 54,
    24, 56, 26, 58, 28, 60, 30, 62, 1, 33, 3, 35, 5, 37, 7, 39, 9, 41, 11, 43, 13, 45, 15, 47,
    17, 49, 19, 51, 21, 53, 23, 55, 25, 57, 27, 59, 29, 61, 31, 63],
  #[0, 1, 17, 16, 4, 5, 21, 20, 8, 9, 25, 24, 12, 13, 29, 28, 3, 2, 18, 19, 7, 6, 22, 23, 11, 10,
    26, 27, 15, 14, 30, 31, 51, 50, 34, 35, 55, 54, 38, 39, 59, 58, 42, 43, 63, 62, 46, 47, 48,
    49, 33, 32, 52, 53, 37, 36, 56, 57, 41, 40, 60, 61, 45, 44],
  #[0, 48, 51, 3, 4, 52, 55, 7, 8, 56, 59, 11, 12, 60, 63, 15, 16, 32, 35, 19, 20, 36, 39, 23,
    24, 40, 43, 27, 28, 44, 47, 31, 17, 33, 34, 18, 21, 37, 38, 22, 25, 41, 42, 26, 29, 45, 46,
    30, 1, 49, 50, 2, 5, 53, 54, 6, 9, 57, 58, 10, 13, 61, 62, 14],
  #[0, 16, 32, 48, 4, 20, 36, 52, 8, 24, 40, 56, 12, 28, 44, 60, 1, 17, 33, 49, 5, 21, 37, 53, 9,
    25, 41, 57, 13, 29, 45, 61, 2, 18, 34, 50, 6, 22, 38, 54, 10, 26, 42, 58, 14, 30, 46, 62, 3,
    19, 35, 51, 7, 23, 39, 55, 11, 27, 43, 59, 15, 31, 47, 63],
  #[0, 1, 16, 17, 4, 5, 20, 21, 8, 9, 24, 25, 12, 13, 28, 29, 2, 3, 18, 19, 6, 7, 22, 23, 10, 11,
    26, 27, 14, 15, 30, 31, 32, 33, 48, 49, 36, 37, 52, 53, 40, 41, 56, 57, 44, 45, 60, 61, 34,
    35, 50, 51, 38, 39, 54, 55, 42, 43, 58, 59, 46, 47, 62, 63],
  #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 17, 16, 19, 18, 21, 20, 23, 22, 25, 24,
    27, 26, 29, 28, 31, 30, 34, 35, 32, 33, 38, 39, 36, 37, 42, 43, 40, 41, 46, 47, 44, 45, 51,
    50, 49, 48, 55, 54, 53, 52, 59, 58, 57, 56, 63, 62, 61, 60]]
@[expose] def extraWordsMinus : List (List ℤ) := [
  [-5, -6, 7, 6, 5],
  [-1, 3, 1],
  [-2, 4, 2],
  [-3, 4, 3],
  [-6, -8, -10, -11, -8, -5, -6, -10, -5, 11, 5, 10, 6, 5],
  [-12, 9, 12],
  [-9, -12, 11, 10, 9]]
@[expose] def chainBaseMinus : List ℕ := [0, 8, 4, 1, 2, 16]

@[expose] def extraStrong : Eps → List (Array ℕ)
  | .plus => extraStrongPlus
  | .minus => extraStrongMinus

@[expose] def extraWords : Eps → List (List ℤ)
  | .plus => extraWordsPlus
  | .minus => extraWordsMinus

@[expose] def chainBase : Eps → List ℕ
  | .plus => chainBasePlus
  | .minus => chainBaseMinus

@[expose] def strong (ε : Eps) : Array (Array ℕ) := genArrs ε ++ (extraStrong ε).toArray

@[expose] def chainWords (ε : Eps) : Array (List ℤ) :=
  (List.replicate 7 ([] : List ℤ) ++ extraWords ε).toArray

@[expose] def nsChainCheck (ε : Eps) : Bool :=
  rawChainOK 64 ((strong ε).extract 0 7) (strong ε) (chainBase ε).toArray (chainWords ε) 1 &&
    (rawOrbitSizes 64 (strong ε) (chainBase ε).toArray).prod == 1451520

@[expose] def actEForm (ε : Eps) (i x : ℕ) : ℕ :=
  if x.testBit 6 then genCode ε i (x % 64) + 64 else genCode ε i (x % 64) ^^^ genCode ε i 0

@[expose] def actETabP : Array (Array ℕ) :=
  Array.ofFn (n := 7) fun i => Array.ofFn (n := 128) fun x => actEForm .plus i x

@[expose] def actETabM : Array (Array ℕ) :=
  Array.ofFn (n := 7) fun i => Array.ofFn (n := 128) fun x => actEForm .minus i x

@[expose] def actETab : Eps → Array (Array ℕ)
  | .plus => actETabP
  | .minus => actETabM

@[expose] def actECode (ε : Eps) (i x : ℕ) : ℕ := ((actETab ε).getD i #[]).getD x 0

@[expose] def mOf : Eps → ℕ
  | .plus => 36
  | .minus => 28

@[expose] def gamArrP : Array ℕ := ((List.range 64).filter fun v => !qfB .plus v).toArray

@[expose] def gamArrM : Array ℕ := ((List.range 64).filter fun v => !qfB .minus v).toArray

@[expose] def gamArr : Eps → Array ℕ
  | .plus => gamArrP
  | .minus => gamArrM

@[expose] def gamIdx (ε : Eps) (v : ℕ) : ℕ := (gamArr ε).toList.idxOf v

@[expose] def permTabP : Array (Array ℕ) :=
  Array.ofFn (n := 7) fun i => Array.ofFn (n := 36) fun g =>
    gamIdx .plus (genCode .plus i (gamArrP.getD g 0))

@[expose] def permTabM : Array (Array ℕ) :=
  Array.ofFn (n := 7) fun i => Array.ofFn (n := 28) fun g =>
    gamIdx .minus (genCode .minus i (gamArrM.getD g 0))

@[expose] def permTab : Eps → Array (Array ℕ)
  | .plus => permTabP
  | .minus => permTabM

@[expose] def permIdx (ε : Eps) (i g : ℕ) : ℕ := ((permTab ε).getD i #[]).getD g 0

@[expose] def nsGamCheck (ε : Eps) : Bool :=
  ((List.range 7).all fun i => (List.range 128).all fun x => actECode ε i x == actEForm ε i x) &&
    (gamArr ε).size == mOf ε &&
    ((List.range 64).all fun v => qfB ε v || (decide (gamIdx ε v < mOf ε) &&
      (gamArr ε).getD (gamIdx ε v) 0 == v)) &&
    (List.range (mOf ε)).all fun g => decide ((gamArr ε).getD g 0 < 64) &&
      !qfB ε ((gamArr ε).getD g 0) && gamIdx ε ((gamArr ε).getD g 0) == g &&
      (List.range 7).all fun i => decide (permIdx ε i g < mOf ε) &&
        (gamArr ε).getD (permIdx ε i g) 0 == genCode ε i ((gamArr ε).getD g 0)


@[expose] def actMCode (ε : Eps) (i y : ℕ) : ℕ :=
  let ta := (actETab ε).getD i #[]
  let tp := (permTab ε).getD i #[]
  foldOr (mOf ε) 7 fun g => ta.getD (blkN 7 y (tp.getD g 0)) 0

@[expose] def foxECode (ε : Eps) (d : ℕ → ℕ) : List ℕ → ℕ
  | [] => 0
  | i :: w => d i ^^^ actECode ε i (foxECode ε d w)

@[expose] def foxMCode (ε : Eps) (d : ℕ → ℕ) : List ℕ → ℕ
  | [] => 0
  | i :: w => d i ^^^ actMCode ε i (foxMCode ε d w)

abbrev nM (ε : Eps) : ℕ := mOf ε * 7

@[expose] def constM (ε : Eps) (x : ℕ) : ℕ := foldOr (mOf ε) 7 fun _ => x

@[expose] def foxMb (ε : Eps) (v : ℕ) : ℕ :=
  foldOr 29 (nM ε) fun j => foxMCode ε (blkN (nM ε) v) (relWords.getD j [])

@[expose] def iotaB (ε : Eps) (v : ℕ) : ℕ := foldOr 29 (nM ε) fun j => constM ε (blkN 7 v j)

@[expose] def foxEb (ε : Eps) (v : ℕ) : ℕ :=
  foldOr 29 7 fun j => foxECode ε (blkN 7 v) (relWords.getD j [])

@[expose] def fmMat (ε : Eps) : Array ℕ := linBits (7 * nM ε) (29 * nM ε) (foxMb ε)

@[expose] def iotaMat (ε : Eps) : Array ℕ := linBits 203 (29 * nM ε) (iotaB ε)

@[expose] def redTab (tab : Array (ℕ × ℕ)) : ℕ → ℕ → ℕ → Option (ℕ × ℕ × ℕ)
  | 0, _, _ => none
  | fuel + 1, v, t =>
    if v = 0 then none else
      let h := Nat.log2 v
      let q := tab.getD h (0, 0)
      if q.1 = 0 then some (h, v, t) else redTab tab fuel (v ^^^ q.1) (t ^^^ q.2)

@[expose] def echelon (b : ℕ) (rows : Array ℕ) : Array (ℕ × ℕ) :=
  (List.range rows.size).foldl (fun tab r =>
    match redTab tab (b + 1) (rows.getD r 0) (2 ^ r) with
    | none => tab
    | some (h, v, t) => tab.set! h (v, t)) (Array.replicate b (0, 0))

@[expose] def annYOf (fm io : Array ℕ) (p b : ℕ) : Array ℕ :=
  let rows := Array.ofFn (n := p) fun r => (fm.getD r 0 <<< 203) ||| io.getD r 0
  ((echelon (b + 203) rows).extract 0 203).filterMap fun q => if q.1 = 0 then none else some q.2

@[expose] def foxECols (ε : Eps) : Array ℕ := Array.ofFn (n := 49) fun k => foxEb ε (2 ^ (k : ℕ))

@[expose] def bIsZero (n : ℕ) (X : Array ℕ) : Bool := (List.range n).all fun i => X.getD i 0 == 0

@[expose] def splitTest (ε : Eps) (p : ℕ) (fm io Y : Array ℕ) : Bool :=
  bIsZero Y.size (bmul Y.size p Y fm) && certCheck 203 49 Y.size (bmul Y.size p Y io) (foxECols ε)

@[expose] def splitCheckOf (ε : Eps) (fm io : Array ℕ) : Bool :=
  splitTest ε (29 * nM ε) fm io (annYOf fm io (29 * nM ε) (7 * nM ε))

@[expose] def nsSplitCheck (ε : Eps) : Bool := splitCheckOf ε (fmMat ε) (iotaMat ε)

@[expose] def cobCol (ε : Eps) (b : ℕ) : ℕ := foldOr 7 7 fun i => actECode ε i (2 ^ b) ^^^ 2 ^ b

@[expose] def nsH1Check (ε : Eps) : Bool :=
  certCheck 49 7 203 (linBits 49 203 (foxEb ε)) (Array.ofFn (n := 7) fun b => cobCol ε b)

end CFSG.EvenSmallLie.OmegaEight.NSplit
