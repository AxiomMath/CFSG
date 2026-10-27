module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallPSp43Model
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallArrChecks
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallQ3F2Gen
public import CFSG.GH74.KGroups.Checks3
public meta import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallPSp43Model
public meta import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallArrChecks
public meta import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallQ3Gen
public meta import CFSG.GH74.KGroups.Checks3
public import Certificates.Certificate2012
public meta import CFSG.LocalAnalysis.ComponentClassification.GSThmB83Outer
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB83Outer

public section

namespace CFSG.ComponentClassification.CatFactsSmall.PSp43

open CFSG.GH74.KGroups CFSG.Certificates CFSG.Sporadic.Schreier Subgroup
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.KGroups.Native
  CFSG.GH74.KGroups.NativeChecks

local notation "P45" => Equiv.Perm (Fin 45)

@[expose] def oddTestA (a : Array ℕ) : Bool :=
  eqA 45 (powA 45 a 9) (idA 45) || eqA 45 (powA 45 a 5) (idA 45)

@[expose] def s045 : P45 :=
  List.formPerm [0, 15] * List.formPerm [1, 35] * List.formPerm [2, 25] * List.formPerm [6, 9] *
    List.formPerm [7, 10] * List.formPerm [8, 11] * List.formPerm [17, 36] *
    List.formPerm [18, 26] * List.formPerm [19, 30] * List.formPerm [21, 40] *
    List.formPerm [22, 44] * List.formPerm [23, 34] * List.formPerm [27, 38] *
    List.formPerm [31, 39] * List.formPerm [32, 43]

@[expose] def admWords : List (List ℤ) :=
    [[], [1, 2, 2, 2], [2, 2, 2, 2, 1], [2], [2, 1, 2, 2, 2], [1], [2, 2], [2, 2, 2], [2, 2, 2, 1],
     [1, 2], [2, 2, 2, 2], [2, 1, 3, 2, 2, 1], [3, 2, 2], [3, 2, 2, 2], [2, 1, 2],
     [1, 2, 3, 2, 1, 2], [2, 3, 2, 2, 2], [3, 2, 1, 2], [1, 2, 1, 2], [2, 3, 2, 1, 2],
     [1, 3, 2, 2, 1], [1, 3, 2, 1, 2], [3, 2, 2, 1], [2, 3, 2, 2, 1], [2, 2, 1, 2, 2, 2], [2, 1],
     [2, 2, 2, 1, 2, 2, 2], [2, 2, 1], [2, 2, 2, 1, 2], [1, 2, 2, 1], [3, 2, 1], [1, 3, 2, 1],
     [2, 2, 1, 2], [3, 2, 2, 1, 2], [1, 2, 1], [2, 1, 3, 2, 1, 2]]

@[expose] def admConj : List P45 :=
  admWords.map fun w => tab (evalCodes [tab x45, tab y45, tab f45] w)

@[expose] def five45A : List (Array ℕ) :=
  (enumA QP45).filter fun a => eqA 45 (powA 45 a 5) (idA 45) && !eqA 45 a (idA 45)

@[expose] def la1 : P45 :=
  List.formPerm [0, 7, 1, 23, 43] * List.formPerm [2, 30, 36, 21, 27] *
    List.formPerm [3, 28, 13, 12, 29] * List.formPerm [4, 5, 16, 33, 41] *
    List.formPerm [6, 44, 11, 31, 18] * List.formPerm [8, 39, 26, 9, 22] *
    List.formPerm [10, 35, 34, 32, 15] * List.formPerm [14, 24, 20, 37, 42] *
    List.formPerm [17, 40, 38, 25, 19]

@[expose] def lb1 : P45 :=
  List.formPerm [0, 22, 6, 7, 23] * List.formPerm [1, 31, 32, 27, 25] *
    List.formPerm [2, 35, 39, 43, 38] * List.formPerm [3, 29, 37, 4, 24] *
    List.formPerm [5, 12, 28, 41, 13] * List.formPerm [8, 30, 21, 18, 36] *
    List.formPerm [9, 10, 34, 15, 44] * List.formPerm [11, 19, 40, 26, 17] *
    List.formPerm [14, 16, 33, 42, 20]

@[expose] def lb2 : P45 :=
  List.formPerm [0, 43, 22, 19, 31] * List.formPerm [1, 36, 6, 26, 2] *
    List.formPerm [3, 13, 20, 24, 14] * List.formPerm [4, 16, 5, 33, 41] *
    List.formPerm [7, 11, 34, 38, 21] * List.formPerm [8, 23, 27, 40, 10] *
    List.formPerm [9, 18, 25, 35, 17] * List.formPerm [12, 29, 37, 28, 42] *
    List.formPerm [15, 32, 44, 30, 39]

@[expose] def l1 : P45 := la1 * lb1 * la1⁻¹ * lb1⁻¹

@[expose] def l2 : P45 := la1 * lb2 * la1⁻¹ * lb2⁻¹

@[expose] def QL45 : RawSchreierDatum 45 :=
  certificate (by decide) [tab l1, tab l2] [[1, 1, 2], [1, 2, 2, 1, 1]] #v[0, 3] (by decide)

@[expose] def q0gens : List P45 :=
  [
    List.formPerm [0, 38, 15, 27] * List.formPerm [1, 40, 34, 2] * List.formPerm [3, 24, 12, 20] *
      List.formPerm [4, 33, 41, 5] * List.formPerm [7, 19, 32, 36] *
      List.formPerm [8, 26, 39, 22] * List.formPerm [10, 30, 43, 17] *
      List.formPerm [11, 18, 31, 44] * List.formPerm [13, 14, 28, 37] *
      List.formPerm [21, 23, 25, 35] * List.formPerm [29, 42],
    List.formPerm [0, 27, 15, 38] * List.formPerm [1, 21, 34, 25] * List.formPerm [2, 35, 40, 23] *
      List.formPerm [3, 20, 12, 24] * List.formPerm [4, 28, 41, 13] *
      List.formPerm [5, 14, 33, 37] * List.formPerm [7, 26, 32, 22] *
      List.formPerm [8, 19, 39, 36] * List.formPerm [10, 18, 43, 44] *
      List.formPerm [11, 30, 31, 17] * List.formPerm [29, 42],
    List.formPerm [0, 27, 15, 38] * List.formPerm [1, 21, 34, 25] * List.formPerm [2, 35, 40, 23] *
      List.formPerm [3, 24, 12, 20] * List.formPerm [4, 33, 41, 5] * List.formPerm [6, 9] *
      List.formPerm [7, 30, 32, 17] * List.formPerm [8, 18, 39, 44] *
      List.formPerm [10, 19, 43, 36] * List.formPerm [11, 26, 31, 22] *
      List.formPerm [13, 14, 28, 37] * List.formPerm [29, 42],
    List.formPerm [0, 15] * List.formPerm [1, 25] * List.formPerm [2, 35] * List.formPerm [3, 12] *
      List.formPerm [4, 13] * List.formPerm [5, 14] * List.formPerm [17, 30] *
      List.formPerm [18, 44] * List.formPerm [19, 36] * List.formPerm [21, 34] *
      List.formPerm [22, 26] * List.formPerm [23, 40] * List.formPerm [28, 41] *
      List.formPerm [29, 42] * List.formPerm [33, 37]]

@[expose] def QQ45 : RawSchreierDatum 45 :=
  certificate (by decide) (q0gens.map tab) [[4]] #v[7, 0] (by decide)

@[expose] def g045 : P45 :=
  List.formPerm [0, 12, 15, 3] * List.formPerm [1, 33, 35, 28] * List.formPerm [2, 41, 25, 37] *
    List.formPerm [4, 21, 14, 40] * List.formPerm [5, 23, 13, 34] * List.formPerm [6, 9] *
    List.formPerm [7, 43, 8, 31] * List.formPerm [10, 39, 11, 32] *
    List.formPerm [17, 22, 44, 36] * List.formPerm [18, 19, 30, 26] *
    List.formPerm [20, 38, 24, 27] * List.formPerm [29, 42]

end CFSG.ComponentClassification.CatFactsSmall.PSp43
