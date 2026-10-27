module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711Pf5Tt48Data

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.TtK

open PkG Chain

@[expose] def rowW (r : List ℕ) : List ℕ := r.drop (4 + r.getD 3 0)

@[expose] def rowG (r : List ℕ) : List ℕ := (r.drop 4).take (r.getD 3 0)

@[expose] def rowVal (r : List ℕ) : ℕ := evalW 64 48 base48 (rowW r)

@[expose] def commP (x a : ℕ) : Bool := comp 64 48 x a == comp 64 48 a x

@[expose] def ccOk (cc x : ℕ) : Bool :=
  let i := SP48.getD 1 (one 64 48)
  let j := SP48.getD 3 (one 64 48)
  let i' := SP48.getD 5 (one 64 48)
  let j' := SP48.getD 7 (one 64 48)
  (cc == 0 && !commP x i) || (cc == 1 && commP x i && !commP x j) ||
    (cc == 2 && commP x i && commP x j && !commP x i') ||
    (cc == 3 && commP x i && commP x j && commP x i' && !commP x j') ||
    (cc == 4 && commP x i && commP x j && commP x i' && commP x j')

@[expose] def rowOk (r : List ℕ) : Bool :=
  let x := rowVal r
  let gx := evalW 64 48 base48 (rowG r)
  let gi := evalW 64 48 base48 (invW6 (rowG r))
  (rowG r ++ rowW r).all (fun l => decide (l < 6)) &&
    ((comp 64 48 x x == tP) == (r.getD 0 0 == 1)) && ccOk (r.getD 1 0) x &&
    comp 64 48 gx (comp 64 48 x gi) == repP.getD (r.getD 2 0) (one 64 48)

@[expose] def cntSq (rows : List (List ℕ)) : ℕ := (rows.filter fun r => r.getD 0 0 == 1).length

@[expose] def cntC2 (rows : List (List ℕ)) : ℕ := (rows.filter fun r => decide (2 ≤ r.getD 1 0)).length

@[expose] def cntC4 (rows : List (List ℕ)) : ℕ := (rows.filter fun r => r.getD 1 0 == 4).length

@[expose] def cnt1 (rows : List (List ℕ)) : ℕ := (rows.filter fun r => S1f.getD (r.getD 2 0) 0 == 1).length

@[expose] def cnt2 (rows : List (List ℕ)) : ℕ := (rows.filter fun r => S2f.getD (r.getD 2 0) 0 == 1).length

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.TtK
