module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallModelConj
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
public import CFSG.GH74.KGroups.Checks
public meta import CFSG.GH74.KGroups.Checks
public meta import Mathlib

public section

namespace CFSG.ComponentClassification.CatFactsSmall.A8

open CFSG.GH74.KGroups CFSG.Certificates CFSG.Sporadic.Schreier Subgroup

local notation "P8" => Equiv.Perm (Fin 8)

@[expose] def s8 : P8 := List.formPerm [0, 1]

@[expose] def c8 : P8 := List.formPerm [0, 1, 2, 3, 4, 5, 6, 7]

@[expose] def a8 : P8 := List.formPerm [0, 1, 2]

@[expose] def b8 : P8 := List.formPerm [1, 2, 3, 4, 5, 6, 7]

@[expose] def QS8 : RawSchreierDatum 8 :=
  certificate (by decide) [tab s8, tab c8]
    [[1, 2], [2, 1, 2, 2, 2, 2, 2, 2, 1], [2, 2, 1, 2, 2, 2, 2, 2, 2], [2, 2, 2, 1, 2, 2, 2, 2, 2],
      [2, 2, 2, 2, 1, 2, 2, 2, 2], [2, 2, 2, 2, 2, 1, 2, 2, 2], [2, 2, 2, 2, 2, 2, 1, 2, 2],
      [2, 2, 2, 1, 2, 2, 2, 2, 2], [2, 2, 2, 2, 1, 2, 2, 2, 2], [2, 2, 2, 2, 2, 1, 2, 2, 2],
      [2, 2, 2, 2, 2, 2, 1, 2, 2], [2, 2, 2, 2, 1, 2, 2, 2, 2], [2, 2, 2, 2, 2, 1, 2, 2, 2],
      [2, 2, 2, 2, 2, 2, 1, 2, 2], [2, 2, 2, 2, 2, 1, 2, 2, 2], [2, 2, 2, 2, 2, 2, 1, 2, 2],
      [2, 2, 2, 2, 2, 2, 1, 2, 2]]
    #v[0, 1, 2, 3, 4, 5, 6] (by decide)

@[expose] def QA8 : RawSchreierDatum 8 :=
  certificate (by decide) [tab a8, tab b8]
    [[2], [1, 2, 1], [1, 2, 1, 2], [2, 2, 2, 2, 2, 1, 2, 1], [2, 2, 1, 2, 1, 2, 2, 2, 2],
      [2, 2, 2, 1, 2, 1, 2, 2, 2], [2, 2, 2, 2, 1, 2, 1, 2, 2], [2, 2, 2, 1, 2, 1, 2, 2, 2],
      [2, 2, 2, 2, 1, 2, 1, 2, 2], [2, 2, 2, 2, 1, 2, 1, 2, 2]]
    #v[0, 1, 2, 3, 4, 5] (by decide)

end CFSG.ComponentClassification.CatFactsSmall.A8
