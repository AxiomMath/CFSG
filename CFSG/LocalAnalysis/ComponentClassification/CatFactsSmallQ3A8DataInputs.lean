module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallQ3A8
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallQ3F2Gen
public import CFSG.GH74.KGroups.Checks3
public meta import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallQ3A8
public meta import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallQ3Gen
public meta import CFSG.GH74.KGroups.Checks3
public import Certificates.Certificate2007
public meta import CFSG.LocalAnalysis.ComponentClassification.GSThmB83Outer
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB83Outer

public section

namespace CFSG.ComponentClassification.CatFactsSmall.A8

open CFSG.GH74.KGroups CFSG.Certificates CFSG.Sporadic.Schreier Subgroup

local notation "P8" => Equiv.Perm (Fin 8)

@[expose] def admWords : List (List ℤ) :=
    [[], [2], [2, 2], [2, 2, 2], [2, 2, 2, 2], [2, 2, 2, 2, 2], [2, 2, 2, 2, 2, 2],
     [2, 2, 2, 2, 2, 2, 2], [1, 2], [1, 2, 2, 2, 2, 2, 2, 2], [2, 2, 2, 2, 2, 2, 1, 2],
     [1, 2, 1, 2, 1, 2, 1, 2], [1, 2, 1, 2, 1, 2], [1, 2, 1, 2], [1, 2, 2, 2, 2, 2, 2, 1, 2],
     [2, 1, 2, 1, 2, 1, 2], [2, 1, 2, 1, 2], [2, 1, 2], [2, 2, 1, 2], [2, 2, 2, 1, 2],
     [2, 2, 2, 2, 1, 2], [2, 2, 2, 2, 2, 1, 2], [2, 1, 2, 2, 2, 2, 2, 2, 1, 2],
     [2, 2, 1, 2, 1, 2, 1, 2], [2, 2, 1, 2, 1, 2], [2, 2, 2, 1, 2, 1, 2, 1, 2],
     [2, 2, 2, 1, 2, 1, 2], [2, 2, 2, 2, 1, 2, 1, 2]]

@[expose] def admConj : List P8 := admWords.map fun w => tab (evalCodes [tab s8, tab c8] w)

@[expose] def five8 : List P8 :=
  (elemsT QA8).filter fun x => decide (x ^ 5 = 1) && !decide (x = 1)

@[expose] def la1 : P8 := List.formPerm [2, 3, 5, 4, 6]

@[expose] def lb1 : P8 := List.formPerm [2, 6, 5, 4, 7]

@[expose] def lb2 : P8 := List.formPerm [2, 5, 4]

@[expose] def l1 : P8 := la1 * lb1 * la1⁻¹ * lb1⁻¹

@[expose] def l2 : P8 := la1 * lb2 * la1⁻¹ * lb2⁻¹

@[expose] def QL8 : RawSchreierDatum 8 :=
  certificate (by decide) [tab l1, tab l2]
    [[1, 1], [1, 2, 2], [2, 1, 1, 2], [1, 1], [1, 2, 1, 1, 2, 2, 2, 2], [2, 1, 2, 2, 2, 2, 1, 1, 2]]
    #v[2, 3, 4, 5] (by decide)

@[expose] def q0gens : List P8 :=
  [List.formPerm [0, 1], List.formPerm [2, 3], List.formPerm [4, 5], List.formPerm [6, 7],
    List.formPerm [2, 4, 3, 5]]

@[expose] def QQ8 : RawSchreierDatum 8 :=
  certificate (by decide) (q0gens.map tab) [[1], [3], [4], [3], [4], [4]] #v[2, 0, 4, 6]
    (by decide)

@[expose] def g08 : P8 := List.formPerm [0, 7, 1, 6] * List.formPerm [2, 5, 3, 4]

end CFSG.ComponentClassification.CatFactsSmall.A8
