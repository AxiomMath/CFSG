module

public import CFSG.GH74.KGroups.L34Aut
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourEnumSpec
public import Certificates.Data.Seitz77CaseB45Data

public section

namespace CFSG.OddStandard.Seitz77.CaseB45

open CFSG.GH74.KGroups CFSG.GH74.KGroups.L34 CFSG.Sporadic.Schreier Certificates.Seitz77CaseB45
  CFSG.ComponentClassification.PSL3Four CFSG.PSL3Four.Native

@[expose] def tl0 : Equiv.Perm (Fin 42) :=
  List.formPerm [0, 18] * List.formPerm [1, 4, 9, 10] * List.formPerm [2, 15, 11, 6] *
    List.formPerm [3, 8, 12, 14] * List.formPerm [5, 7, 13, 16] * List.formPerm [19, 20] *
    List.formPerm [21, 37] * List.formPerm [22, 41, 38, 25] * List.formPerm [23, 29, 39, 31] *
    List.formPerm [24, 33, 40, 28] * List.formPerm [26, 32, 30, 27] * List.formPerm [35, 36]

@[expose] def tl1 : Equiv.Perm (Fin 42) :=
  List.formPerm [0, 37] * List.formPerm [1, 39] * List.formPerm [2, 32] * List.formPerm [3, 24] *
    List.formPerm [4, 26] * List.formPerm [5, 33] * List.formPerm [6, 29] *
    List.formPerm [7, 22] * List.formPerm [8, 41] * List.formPerm [9, 23] *
    List.formPerm [10, 30] * List.formPerm [11, 27] * List.formPerm [12, 40] *
    List.formPerm [13, 28] * List.formPerm [14, 25] * List.formPerm [15, 31] *
    List.formPerm [16, 38] * List.formPerm [17, 34] * List.formPerm [18, 36] *
    List.formPerm [19, 35] * List.formPerm [20, 21]

@[expose] def tl2 : Equiv.Perm (Fin 42) :=
  List.formPerm [0, 21, 18, 36] * List.formPerm [1, 25, 2, 22, 13, 32, 14, 30] *
    List.formPerm [3, 23, 7, 40, 15, 33, 10, 29] * List.formPerm [4, 24, 12, 28, 16, 31, 6, 39] *
    List.formPerm [5, 41, 8, 38, 9, 27, 11, 26] * List.formPerm [17, 34] *
    List.formPerm [19, 35, 20, 37]

@[expose] def u0 : Equiv.Perm (Fin 42) :=
  List.formPerm [0, 20] * List.formPerm [1, 12, 9, 3] * List.formPerm [2, 16, 11, 7] *
    List.formPerm [4, 8, 10, 14] * List.formPerm [5, 15, 13, 6] * List.formPerm [18, 19] *
    List.formPerm [21, 35] * List.formPerm [22, 23, 38, 39] * List.formPerm [24, 32, 40, 27] *
    List.formPerm [25, 29, 41, 31] * List.formPerm [26, 28, 30, 33] * List.formPerm [36, 37]

@[expose] def u1 : Equiv.Perm (Fin 42) :=
  List.formPerm [0, 20] * List.formPerm [1, 9] * List.formPerm [2, 14] * List.formPerm [4, 7] *
    List.formPerm [5, 13] * List.formPerm [8, 11] * List.formPerm [10, 16] *
    List.formPerm [18, 19] * List.formPerm [22, 39] * List.formPerm [23, 38] *
    List.formPerm [24, 41] * List.formPerm [25, 40] * List.formPerm [26, 33] *
    List.formPerm [27, 31] * List.formPerm [28, 30] * List.formPerm [29, 32]

@[expose] def u2 : Equiv.Perm (Fin 42) :=
  List.formPerm [0, 18] * List.formPerm [1, 4, 9, 10] * List.formPerm [2, 15, 11, 6] *
    List.formPerm [3, 8, 12, 14] * List.formPerm [5, 7, 13, 16] * List.formPerm [19, 20] *
    List.formPerm [21, 37] * List.formPerm [22, 41, 38, 25] * List.formPerm [23, 29, 39, 31] *
    List.formPerm [24, 33, 40, 28] * List.formPerm [26, 32, 30, 27] * List.formPerm [35, 36]

@[expose] def u3 : Equiv.Perm (Fin 42) :=
  List.formPerm [0, 20] * List.formPerm [1, 10, 13, 7] * List.formPerm [2, 15, 14, 3] *
    List.formPerm [4, 5, 16, 9] * List.formPerm [6, 8, 12, 11] * List.formPerm [18, 19] *
    List.formPerm [21, 37] * List.formPerm [22, 28, 30, 39] * List.formPerm [23, 38, 33, 26] *
    List.formPerm [24, 25, 31, 32] * List.formPerm [27, 40, 41, 29] * List.formPerm [35, 36]


theorem tabRep_tl0 : TabRep tlGens[0]! tl0 := by unfold TabRep; decide +kernel

theorem tabRep_tl1 : TabRep tlGens[1]! tl1 := by unfold TabRep; decide +kernel

theorem tabRep_tl2 : TabRep tlGens[2]! tl2 := by unfold TabRep; decide +kernel

theorem tabRep_u0 : TabRep uGens[0]! u0 := by unfold TabRep; decide +kernel

theorem tabRep_u1 : TabRep uGens[1]! u1 := by unfold TabRep; decide +kernel

theorem tabRep_u2 : TabRep uGens[2]! u2 := by unfold TabRep; decide +kernel

theorem tabRep_u3 : TabRep uGens[3]! u3 := by unfold TabRep; decide +kernel

@[expose] def TLsub : Subgroup (Equiv.Perm (Fin 42)) := Subgroup.closure {tl0, tl1, tl2}

@[expose] def Usub0 : Subgroup (Equiv.Perm (Fin 42)) := Subgroup.closure {u0, u1, u2, u3}

theorem tl0_mem : tl0 ∈ QA.originalSubgroup :=
  (mem_iff_sift QA QA_ok tl0).2 (by decide +kernel)

theorem tl1_mem : tl1 ∈ QA.originalSubgroup :=
  (mem_iff_sift QA QA_ok tl1).2 (by decide +kernel)

theorem tl2_mem : tl2 ∈ QA.originalSubgroup :=
  (mem_iff_sift QA QA_ok tl2).2 (by decide +kernel)

theorem u0_mem : u0 ∈ QP.originalSubgroup :=
  (mem_iff_sift QP QP_ok u0).2 (by decide +kernel)

theorem u1_mem : u1 ∈ QP.originalSubgroup :=
  (mem_iff_sift QP QP_ok u1).2 (by decide +kernel)

theorem u2_mem : u2 ∈ QP.originalSubgroup :=
  (mem_iff_sift QP QP_ok u2).2 (by decide +kernel)

theorem u3_mem : u3 ∈ QP.originalSubgroup :=
  (mem_iff_sift QP QP_ok u3).2 (by decide +kernel)


end CFSG.OddStandard.Seitz77.CaseB45
