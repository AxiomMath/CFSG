module

public import CFSG.LieType.Multipliers.F42Data

public section

namespace CFSG.KC.Misc.F42

open CFSG.LieType.Multipliers.F42 CFSG.F3.Native CFSG.Blueprint.Chevalley

@[expose] def slpValsOf (pA pB slp : String) : Array Pair :=
  (pairUp (parseInts slp)).foldl slpStep
    #[(rowsOf 52 pA, rowsOf 52 pA), (rowsOf 52 pB, mul 52 (rowsOf 52 pB) (rowsOf 52 pB))]

@[expose] def liftsOf (pA pB slp : String) (refs : List ℤ) : Array Pair :=
  (refs.map (refVal (slpValsOf pA pB slp))).toArray

@[expose] def rootAtG (R : List (List ℤ)) (k : ℕ) : Fin Tag.F4.rank → ℤ :=
  fun t => (R.getD k []).getD t.val 0

@[expose] def isRootBG (R : List (List ℤ)) (v : Fin Tag.F4.rank → ℤ) : Bool :=
  decide (List.ofFn v ∈ R)

@[expose] def rootIdxG (R : List (List ℤ)) (v : Fin Tag.F4.rank → ℤ) : ℕ := R.idxOf (List.ofFn v)

@[expose] def factorG (R : List (List ℤ)) (L : Array Pair) (c : Bool) (v : Fin Tag.F4.rank → ℤ) :
    Array V :=
  if c && isRootBG R v then matOf L (rootIdxG R v) else idM 52

@[expose] def prodArrG (R : List (List ℤ)) (L : Array Pair) (i j : ℕ) : Array V :=
  mul 52 (mul 52 (factorG R L (!isRootBG R (rootAtG R j - rootAtG R i)) (rootAtG R i + rootAtG R j))
    (factorG R L true (rootAtG R i + 2 • rootAtG R j)))
    (factorG R L true (2 • rootAtG R i + rootAtG R j))

@[expose] def pairOKG (R : List (List ℤ)) (L : Array Pair) (i j : ℕ) : Bool :=
  eqPM (commArr L i j) (prodArrG R L i j) &&
    commutes (factorG R L (!isRootBG R (rootAtG R j - rootAtG R i)) (rootAtG R i + rootAtG R j))
      (factorG R L true (rootAtG R i + 2 • rootAtG R j)) &&
    commutes (factorG R L (!isRootBG R (rootAtG R j - rootAtG R i)) (rootAtG R i + rootAtG R j))
      (factorG R L true (2 • rootAtG R i + rootAtG R j)) &&
    commutes (factorG R L true (rootAtG R i + 2 • rootAtG R j))
      (factorG R L true (2 • rootAtG R i + rootAtG R j))

@[expose] def pairsOKG (R : List (List ℤ)) (L : Array Pair) : Bool :=
  (List.range 48).all fun i => (List.range 48).all fun j =>
    i == j || decide (rootAtG R i + rootAtG R j = 0) || pairOKG R L i j

@[expose] def wordOKG (R : List (List ℤ)) (CP : List (ℕ × ℕ)) (L : Array Pair) (k : ℕ) : Bool :=
  let p := CP.getD k (0, 0)
  p.1 < 48 && p.2 < 48 && p.1 != p.2 && !decide (rootAtG R p.1 + rootAtG R p.2 = 0) &&
    decide (rootAtG R p.1 + rootAtG R p.2 = rootAtG R k) &&
    !isRootBG R (rootAtG R p.1 + 2 • rootAtG R p.2) &&
    !isRootBG R (2 • rootAtG R p.1 + rootAtG R p.2) &&
    !isRootBG R (rootAtG R p.2 - rootAtG R p.1) &&
    eqM 52 (commArr L p.1 p.2) (matOf L k)

@[expose] def negOKG (R : List (List ℤ)) (L : Array Pair) (i j : ℕ) : Bool :=
  i < 48 && j < 48 && i != j && !decide (rootAtG R i + rootAtG R j = 0) &&
    eqM 52 (commArr L i j) (negM (prodArrG R L i j))

@[expose] def strOf (l : List ℕ) : String := String.ofList (l.map Char.ofNat)

@[expose] def refOfCode (c : ℕ) : ℤ := if c % 2 = 0 then (c / 2 : ℕ) else -((c / 2 : ℕ) : ℤ) - 1

end CFSG.KC.Misc.F42

end
