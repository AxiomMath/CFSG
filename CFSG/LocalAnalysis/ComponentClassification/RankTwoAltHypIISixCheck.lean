module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.A6FactsCore2

public section

namespace CFSG.ComponentClassification.RankTwoAlt.Six

open CFSG.QuasithinUnique.A6Facts.Core

@[expose] def tFrobTC : List Nat := [0, 6, 3, 2, 8, 5, 1, 7, 4, 9]

@[expose] def t0C : List Nat := [1, 0, 3, 2, 9, 6, 5, 8, 7, 4]

@[expose] def v0C : List Nat := [0, 1, 9, 4, 3, 8, 7, 6, 5, 2]

@[expose] def f1bC : List Nat := [1, 0, 9, 3, 4, 8, 6, 7, 5, 2]

@[expose] def tMulC' : List Nat := [0, 4, 8, 5, 6, 1, 7, 2, 3, 9]

@[expose] def cFrobL : List (List Nat) :=
    [[9, 1, 2, 6, 5, 4, 3, 8, 7, 0], [2, 1, 9, 7, 8, 3, 4, 5, 6, 0],
     [9, 2, 1, 6, 4, 5, 3, 7, 8, 0], [9, 0, 1, 5, 7, 6, 8, 4, 3, 2],
     [9, 2, 0, 7, 3, 5, 4, 6, 8, 1], [2, 1, 0, 5, 4, 3, 8, 7, 6, 9],
     [9, 2, 0, 4, 6, 8, 7, 3, 5, 1], [1, 2, 0, 7, 8, 6, 4, 5, 3, 9],
     [2, 0, 1, 8, 6, 7, 5, 3, 4, 9], [9, 0, 2, 4, 8, 6, 7, 5, 3, 1],
     [9, 1, 2, 3, 8, 7, 6, 5, 4, 0], [2, 0, 1, 5, 3, 4, 8, 6, 7, 9],
     [0, 9, 2, 5, 7, 3, 8, 4, 6, 1], [0, 9, 1, 7, 5, 6, 4, 8, 3, 2],
     [1, 9, 0, 6, 5, 7, 3, 8, 4, 2], [2, 9, 1, 7, 3, 8, 4, 6, 5, 0],
     [2, 9, 0, 6, 4, 8, 3, 7, 5, 1], [2, 9, 0, 3, 7, 5, 6, 4, 8, 1],
     [9, 0, 1, 8, 4, 3, 5, 7, 6, 2], [9, 0, 2, 7, 5, 3, 4, 8, 6, 1],
     [1, 2, 9, 5, 4, 6, 8, 7, 3, 0], [0, 1, 2, 6, 7, 8, 3, 4, 5, 9],
     [1, 2, 0, 4, 5, 3, 7, 8, 6, 9], [2, 0, 9, 3, 5, 7, 6, 8, 4, 1],
     [1, 0, 9, 3, 4, 8, 6, 7, 5, 2], [1, 0, 9, 6, 7, 5, 3, 4, 8, 2],
     [0, 2, 9, 5, 3, 7, 8, 6, 4, 1], [0, 1, 2, 3, 4, 5, 6, 7, 8, 9],
     [0, 9, 2, 8, 4, 6, 5, 7, 3, 1], [0, 1, 9, 7, 6, 5, 4, 3, 8, 2],
     [1, 9, 2, 5, 6, 4, 8, 3, 7, 0], [9, 1, 0, 8, 3, 4, 5, 6, 7, 2],
     [1, 9, 0, 3, 8, 4, 6, 5, 7, 2], [2, 0, 9, 6, 8, 4, 3, 5, 7, 1],
     [1, 2, 9, 8, 7, 3, 5, 4, 6, 0], [0, 2, 9, 8, 6, 4, 5, 3, 7, 1],
     [2, 1, 9, 4, 5, 6, 7, 8, 3, 0], [0, 1, 9, 4, 3, 8, 7, 6, 5, 2],
     [9, 1, 0, 5, 6, 7, 8, 3, 4, 2], [2, 1, 0, 8, 7, 6, 5, 4, 3, 9],
     [2, 9, 1, 4, 6, 5, 7, 3, 8, 0], [1, 0, 2, 7, 6, 8, 4, 3, 5, 9],
     [0, 2, 1, 6, 8, 7, 3, 5, 4, 9], [9, 2, 1, 3, 7, 8, 6, 4, 5, 0],
     [0, 9, 1, 4, 8, 3, 7, 5, 6, 2], [0, 2, 1, 3, 5, 4, 6, 8, 7, 9],
     [1, 0, 2, 4, 3, 5, 7, 6, 8, 9], [1, 9, 2, 8, 3, 7, 5, 6, 4, 0]]

@[expose] def c0L : List (List Nat) :=
    [[9, 4, 3, 2, 6, 7, 8, 0, 1, 5], [2, 3, 8, 7, 9, 1, 0, 5, 6, 4],
     [2, 3, 5, 6, 1, 7, 8, 4, 9, 0], [9, 4, 0, 1, 7, 2, 3, 5, 6, 8],
     [2, 3, 0, 1, 6, 9, 4, 8, 7, 5], [7, 8, 5, 6, 9, 2, 3, 0, 1, 4],
     [6, 5, 8, 7, 2, 9, 4, 0, 1, 3], [8, 7, 1, 0, 3, 5, 6, 9, 4, 2],
     [8, 7, 9, 4, 5, 0, 1, 2, 3, 6], [1, 0, 3, 2, 9, 6, 5, 8, 7, 4],
     [5, 6, 2, 3, 8, 0, 1, 9, 4, 7], [3, 2, 1, 0, 5, 4, 9, 7, 8, 6],
     [3, 2, 6, 5, 0, 8, 7, 9, 4, 1], [0, 1, 7, 8, 5, 3, 2, 9, 4, 6],
     [8, 7, 6, 5, 4, 3, 2, 1, 0, 9], [6, 5, 0, 1, 9, 7, 8, 3, 2, 4],
     [7, 8, 4, 9, 6, 1, 0, 3, 2, 5], [8, 7, 2, 3, 0, 4, 9, 6, 5, 1],
     [5, 6, 7, 8, 3, 4, 9, 1, 0, 2], [4, 9, 2, 3, 5, 8, 7, 1, 0, 6],
     [4, 9, 7, 8, 0, 5, 6, 2, 3, 1], [0, 1, 2, 3, 4, 5, 6, 7, 8, 9],
     [1, 0, 5, 6, 7, 9, 4, 3, 2, 8], [1, 0, 8, 7, 6, 2, 3, 4, 9, 5],
     [3, 2, 9, 4, 8, 5, 6, 1, 0, 7], [4, 9, 1, 0, 8, 3, 2, 6, 5, 7],
     [9, 4, 5, 6, 2, 1, 0, 8, 7, 3], [0, 1, 6, 5, 8, 4, 9, 2, 3, 7],
     [6, 5, 3, 2, 7, 1, 0, 4, 9, 8], [4, 9, 6, 5, 3, 0, 1, 7, 8, 2],
     [0, 1, 9, 4, 3, 8, 7, 6, 5, 2], [3, 2, 7, 8, 4, 0, 1, 6, 5, 9],
     [9, 4, 8, 7, 1, 6, 5, 3, 2, 0], [1, 0, 4, 9, 2, 7, 8, 5, 6, 3],
     [5, 6, 9, 4, 0, 3, 2, 7, 8, 1], [7, 8, 3, 2, 1, 9, 4, 5, 6, 0],
     [6, 5, 4, 9, 1, 2, 3, 8, 7, 0], [5, 6, 1, 0, 4, 8, 7, 2, 3, 9],
     [7, 8, 0, 1, 2, 6, 5, 4, 9, 3], [2, 3, 4, 9, 7, 6, 5, 0, 1, 8]]

theorem tMul_tFrobT : cmul tMulC' tFrobTC = cmul tFrobC tMulC' := by decide +kernel

theorem cFrobL_check : cFrobL.all (fun h => cmul h tFrobC == cmul tFrobC h && autL.contains h) =
    true := by
  decide +kernel

theorem c0L_check : c0L.all (fun h => cmul h t0C == cmul t0C h && autL.contains h) = true := by
  decide +kernel

theorem outer_conj_check : autL.all (fun c => cmul c c != cid || pslLit.contains c ||
    pslLit.any fun g => cmul g c == cmul tFrobC g || cmul g c == cmul tFrobTC g ||
      cmul g c == cmul t0C g) = true := by
  decide +kernel

theorem frob_cent_check : autL.all (fun c => cmul c c != cid || c == cid || c == tFrobC ||
    cmul c tFrobC != cmul tFrobC c ||
    cFrobL.any fun h => cmul h c == cmul v0C h || cmul h c == cmul (cmul tFrobC v0C) h ||
      cmul h c == cmul f1bC h || cmul h c == cmul (cmul tFrobC f1bC) h) = true := by
  decide +kernel

theorem pgl_cent_check : autL.all (fun c => cmul c c != cid || c == cid || c == t0C ||
    cmul c t0C != cmul t0C c ||
    c0L.any fun h => cmul h c == cmul v0C h || cmul h c == cmul (cmul t0C v0C) h) = true := by
  decide +kernel

end CFSG.ComponentClassification.RankTwoAlt.Six
