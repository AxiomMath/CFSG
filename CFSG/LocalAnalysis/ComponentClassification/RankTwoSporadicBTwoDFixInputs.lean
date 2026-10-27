module

public import CFSG.Monster.B.TwoA.Sp8.QuadCosetCInputs

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.B.TwoDFix

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.Co2
  CFSG.Monster.B.TwoA.Sp8 CFSG.Monster.B.Rep4371

@[expose] def actWord (w : List ℕ) (x : ℕ) : ℕ :=
  w.foldr (fun k x => Native.actD 8 (genArr k) x) x

@[expose] def wordConj (w : List ℕ) (y : Model.Pauli) : Model.Pauli :=
  w.foldr (fun k y => h1ConjN k y) y

@[expose] def liftRows (k : ℕ) : Array ℕ :=
  if 23 ≤ k ∧ k < 44 then Co2Inv.cRows (k - 23) else Co2Inv.idRows

@[expose] def wordRows (w : List ℕ) : Array ℕ :=
  w.foldr (fun k A => Co2Inv.rowsMul A (liftRows k)) Co2Inv.idRows

@[expose] def rowKey (w : List ℕ) : List ℕ :=
  let R := wordRows w
  (List.range 22).map fun t => R[t]!

@[expose] def keyOK (key : List ℕ) : Bool := key.all fun r => decide (r < 2 ^ 22)

@[expose] def pauliVec (w : List ℕ) : Model.Pauli :=
  w.foldr (fun k x => Model.Pauli.mul (pauliGen k) x) (false, 0, 0)

@[expose] def subWord (gs : List (List ℕ)) (m : ℕ) : List ℕ :=
  ((List.range gs.length).filter fun i => m.testBit i).flatMap fun i => gs.getD i []

@[expose] def redW (y : Model.Pauli) : ℕ × ℕ :=
  (y.2.1, if y.2.2.testBit 0 then y.2.2 ^^^ 191 else y.2.2)

@[expose] def boxed (y : Model.Pauli) : Bool := decide (y.2.1 < 4096) && decide (y.2.2 < 4096)

@[expose] def coGens : List (List ℕ) :=
  [[23], [24], [25], [26], [32], [41], [42], [33, 35], [33, 36]]

@[expose] def pauliWords : List (List ℕ) :=
  [[0], [9], [10], [17], [18], [19], [20], [21], [22], [1, 2], [1, 3], [1, 4], [11, 12],
    [13, 14], [13, 15]]

@[expose] def pauliProd (m : ℕ) : Model.Pauli := pauliVec (subWord pauliWords m)

@[expose] def duals : List (ℕ × ℕ) :=
  [(2, 0), (1024, 0), (2048, 0), (0, 64), (0, 160), (0, 256), (0, 512), (0, 1024), (0, 2048),
    (8, 0), (16, 0), (32, 0), (0, 32), (0, 40), (0, 48)]

@[expose] def decodeW (x : ℕ × ℕ) : ℕ :=
  (List.range 15).foldl (fun acc i =>
    let f := duals.getD i (0, 0)
    if Model.pairN f.1 x.1 ^^ Model.pairN f.2 x.2 then acc + 2 ^ i else acc) 0

@[expose] def wWord : List ℕ := [3, 27, 29, 28, 35, 35]

@[expose] def sWord : List ℕ := wWord ++ wWord ++ wWord ++ wWord

@[expose] def cPauli : Model.Pauli := (false, 0, 127)

@[expose] def u7Elts (m : ℕ) : List Model.Pauli :=
  [foldP (bvec 8 m), Model.Pauli.mul (foldP (bvec 8 m)) cPauli]

@[expose] def u7Idx : List ℕ :=
  ((List.range 256).flatMap fun m => (u7Elts m).map fun u => decodeW (redW u)).dedup

@[expose] def pauliBasis (i : ℕ) : Model.Pauli := pauliVec (pauliWords.getD i [])

@[expose] def commS (y : Model.Pauli) : Model.Pauli := Model.Pauli.mul (wordConj sWord y) y

@[expose] def commRows : Array ℕ :=
  #[80, 23054, 15366, 4184, 4184, 96, 112, 24632, 20808, 26430, 12778, 22148, 4104, 320, 12744]

@[expose] def rowsCheck : Bool :=
  (coGens ++ pauliWords).all fun w => (List.range 256).all fun x => actWord w x == x

@[expose] def qCheck : Bool :=
  let keys := (List.range 512).map fun m => rowKey (subWord coGens m)
  keys.Nodup && keys.all keyOK

@[expose] def alphaCheck : Bool :=
  (List.range 512).all fun m =>
    let a := rowKey (sWord ++ subWord coGens m)
    let b := rowKey (subWord coGens m ++ sWord)
    let c := rowKey ([32] ++ subWord coGens m ++ sWord)
    keyOK a && keyOK b && keyOK c && ((!(a == b) && !(a == c)) || m == 0 || m == 16)

@[expose] def pauliCheck : Bool :=
  (List.range 32768).all fun m => decodeW (redW (pauliProd m)) == m && boxed (pauliProd m)

@[expose] def commCheck : Bool :=
  (List.range 15).all fun i =>
    let c := commS (pauliBasis i)
    boxed c && decide (commRows[i]! < 32768) && redW (pauliProd commRows[i]!) == redW c

@[expose] def u7Check : Bool :=
  (List.range 256).all fun m => (u7Elts m).all fun u =>
    decide (decodeW (redW u) < 32768) && redW (pauliProd (decodeW (redW u))) == redW u

@[expose] def betaCheck : Bool :=
  (List.range 32768).all fun m =>
    decide (Native.actD 15 commRows m < 32768) &&
      (!(u7Idx.contains (Native.actD 15 commRows m)) || u7Idx.contains m)

@[expose] def sCheck : Bool :=
  ((List.range 256).all fun x =>
    decide (actWord sWord x < 256) && qN (actWord sWord x ^^^ 64) == qN (x ^^^ 64)) &&
    rowKey (wWord ++ wWord ++ wWord ++ wWord ++ wWord) == rowKey []

end CFSG.ComponentClassification.RankTwoSporadic.B.TwoDFix
