module

public import CFSG.Literature.GL52Lookup
public import CFSG.Literature.GL52Elements
public meta import CFSG.Literature.GL52Lookup
public meta import CFSG.Literature.GL52Elements

public section

namespace CFSG.Literature.GL52

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native

@[expose] def r0Gens : List G := [glTau2, glTauB]

@[expose] def r0Words : List (List ℤ) :=
  [[], [1], [1, 1], [2], [1, 2], [1, 1, 2], [2, 2], [1, 2, 2], [1, 1, 2, 2]]

@[expose] def r0Elts : List G := r0Words.map (wordG (letterG r0Gens))

@[expose] def fpT (T : Table) : ℕ := (List.range 31).countP fun i => ap T i == i

@[expose] def cmtT (T X : Table) : Bool := tblEq 31 (compT 31 T X) (compT 31 X T)

end CFSG.Literature.GL52
