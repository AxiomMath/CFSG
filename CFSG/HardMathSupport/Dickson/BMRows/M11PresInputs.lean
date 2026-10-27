module

public import CFSG.Certificates.CosetTablePresented

public section

namespace CFSG.HardMathSupport.Dickson.BMRows.M11

open CFSG.CosetTable

@[expose] def m11Rels : List (List (Fin 4 × Bool)) :=
  [[(0, true), (0, true), (0, true), (0, true)],
    [(1, true), (1, true), (1, true), (1, true)],
    [(2, true), (2, true)],
    [(3, true), (3, true)],
    [(0, false), (1, false), (0, true), (1, true)],
    [(2, true), (0, true), (2, true), (1, false)],
    [(3, true), (0, true), (3, true), (0, true)],
    [(3, true), (1, true), (3, true), (1, true)],
    [(2, false), (3, false), (2, true), (3, true)]]

@[expose] def m11CosetCheck (_ : Unit := ()) : Bool := subsetCheck m11Rels [] 4096 64

end CFSG.HardMathSupport.Dickson.BMRows.M11
