module

public import CFSG.Fischer.Classification.PartIII.Beta.Data
public import CFSG.Sporadic.Schreier.Enumeration
public import Mathlib

public section

namespace CFSG.ComponentClassification.CatFactsSmall.PSp43

open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Fischer.Classification.Beta

local notation "P45" => Equiv.Perm (Fin 45)

@[expose] def tauFun (i j : Fin 45) : Fin 45 := uIdx (tU (uPt i) (uPt j))

theorem tauFun_tauFun (i j : Fin 45) : tauFun i (tauFun i j) = j := by
  revert i j
  decide +kernel

@[expose] def tauPerm (i : Fin 45) : P45 :=
  ⟨tauFun i, tauFun i, tauFun_tauFun i, tauFun_tauFun i⟩

@[expose] def x45 : P45 := tauPerm 0

@[expose] def y45 : P45 := tauPerm 31 * tauPerm 5 * tauPerm 36 * tauPerm 44

@[expose] def f45 : P45 :=
  List.formPerm [1, 2] * List.formPerm [4, 5] * List.formPerm [7, 8] * List.formPerm [10, 11] *
    List.formPerm [13, 14] * List.formPerm [17, 18] * List.formPerm [19, 22] *
    List.formPerm [20, 24] * List.formPerm [21, 23] * List.formPerm [25, 35] *
    List.formPerm [26, 36] * List.formPerm [27, 38] * List.formPerm [28, 37] *
    List.formPerm [29, 42] * List.formPerm [30, 44] * List.formPerm [31, 43] *
    List.formPerm [32, 39] * List.formPerm [33, 41] * List.formPerm [34, 40]

@[expose] def QP45 : RawSchreierDatum 45 :=
  certificate (by decide) [tab x45, tab y45]
    [[1], [2, 1, 2, 2, 2, 2, 1, 2], [2, 1, 2, 1, 2, 2, 2, 1, 2], [1, 2, 1, 2, 2, 2, 1, 2, 1, 2],
      [1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2],
      [2, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 2, 2]]
    #v[0, 1, 16, 3] (by decide)

@[expose] def QA45 : RawSchreierDatum 45 :=
  certificate (by decide) [tab x45, tab y45, tab f45]
    [[1], [3], [2, 2, 2, 3, 2, 2], [2, 1, 2, 3, 2, 3, 2], [1, 3], [1, 2, 3, 2, 3, 2, 3, 2],
      [1, 2, 1, 2, 2, 2, 1, 2, 1, 2], [2, 1, 2, 3, 2, 2, 3, 2, 1, 2, 1, 2, 2]]
    #v[0, 1, 3, 9] (by decide)

@[expose] def ws45 : List (List Bool × ℕ) :=
  [([false, true], 9), ([false, true, true], 12), ([false, true, false, true, true], 6)]

end CFSG.ComponentClassification.CatFactsSmall.PSp43
