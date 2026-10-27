module

public import CFSG.GH74.Generic.Certificates
public import CFSG.GH74.Filter.Sporadic.PermSpec
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalInputs

public section

namespace CFSG.GH74.E2

open CFSG.GH74.Generic CFSG.Blueprint CFSG.SectionRank CFSG.SectionRank.Native

@[expose] def m22Perm : PermData where
  seedA := #[12, 7, 15, 11, 4, 21, 16, 1, 9, 8, 13, 3, 0, 10, 14, 2, 6, 17, 18, 19, 20, 5]
  seedB := #[21, 17, 20, 12, 11, 10, 14, 13, 8, 7, 6, 4, 1, 19, 5, 15, 18, 3, 16, 9, 0, 2]
  nregs := 51
  prog := [
      .pow 3 1 2, .mul 0 2 3, .mul 3 0 4, .mul 4 1 5, .mul 5 0 6, .mul 2 0 7, .mul 7 1 8,
      .mul 8 0 9, .mul 9 2 10, .mul 10 0 11, .mul 11 1 12, .mul 1 0 13, .mul 13 2 14, .mul 14 0 15,
      .mul 15 1 16, .mul 16 0 17, .mul 17 1 18, .mul 18 0 19, .mul 19 1 20, .mul 20 0 21,
      .mul 21 2 22, .mul 22 0 23, .mul 23 2 24, .mul 24 0 25, .mul 25 2 26, .mul 26 0 27,
      .mul 27 1 28, .mul 28 0 29, .mul 29 2 30, .mul 1 1 31, .mul 31 0 32, .mul 32 1 33,
      .mul 33 0 34, .mul 34 2 35, .mul 35 0 36, .mul 36 2 37, .mul 37 0 38, .mul 38 2 39,
      .mul 39 0 40, .mul 40 1 41, .mul 41 0 42, .mul 42 1 43, .mul 43 0 44, .mul 44 1 45,
      .mul 45 0 46, .mul 46 2 47, .mul 47 0 48, .mul 48 1 49, .mul 49 1 50]
  outs := [6, 12, 30, 50]

theorem m22_permCheck : permCheck 22 m22Perm = true := by decide +kernel

theorem rankCertified_M22 : RankCertified NativeSporadic.M22 3 := by
  obtain ⟨r, hr, x, hsq, hcomm, hker⟩ := exists_of_permCheck m22Perm
    (σA := List.formPerm [0, 12] * List.formPerm [1, 7] * List.formPerm [2, 15] *
      List.formPerm [3, 11] * List.formPerm [5, 21] * List.formPerm [6, 16] *
      List.formPerm [8, 9] * List.formPerm [10, 13])
    (σB := List.formPerm [0, 21, 2, 20] * List.formPerm [1, 17, 3, 12] * List.formPerm [4, 11] *
      List.formPerm [5, 10, 6, 14] * List.formPerm [7, 13, 19, 9] * List.formPerm [16, 18])
    (by decide +kernel) (by decide +kernel) m22_permCheck
  have h4 : r = 4 := hr
  subst h4
  exact rankCertified_of_commuting_involutions x hsq hcomm hker (by norm_num)

theorem rankCertified_of_isSporadic_M22 {S : Type} [Group S]
    (h : NativeSporadic.IsSporadic S .M22) : RankCertified S 3 := by
  obtain ⟨e⟩ := h
  exact rankCertified_M22.of_mulEquiv e.symm

@[expose] def m23Perm : PermData where
  seedA := #[1, 0, 3, 2, 4, 5, 7, 6, 9, 8, 10, 11, 13, 12, 15, 14, 16, 17, 19, 18, 21, 20, 22]
  seedB := #[15, 8, 0, 4, 7, 21, 6, 22, 20, 9, 2, 1, 19, 17, 16, 10, 14, 5, 18, 12, 11, 13, 3]
  nregs := 43
  prog := [
      .pow 3 1 2, .mul 1 0 3, .mul 3 1 4, .mul 4 1 5, .mul 5 0 6, .mul 6 2 7, .mul 0 1 8,
      .mul 8 0 9, .mul 9 1 10, .mul 10 1 11, .mul 11 0 12, .mul 12 2 13, .mul 13 0 14, .mul 2 0 15,
      .mul 15 1 16, .mul 16 0 17, .mul 17 1 18, .mul 18 0 19, .mul 19 1 20, .mul 20 1 21,
      .mul 21 0 22, .mul 22 2 23, .mul 23 0 24, .mul 24 2 25, .mul 25 0 26, .mul 26 1 27,
      .mul 0 2 28, .mul 28 0 29, .mul 29 1 30, .mul 30 0 31, .mul 31 1 32, .mul 32 0 33,
      .mul 33 1 34, .mul 34 1 35, .mul 35 0 36, .mul 36 2 37, .mul 37 0 38, .mul 38 2 39,
      .mul 39 0 40, .mul 40 1 41, .mul 41 0 42]
  outs := [7, 14, 27, 42]

theorem m23_permCheck : permCheck 23 m23Perm = true := by decide +kernel

theorem rankCertified_M23 : RankCertified NativeSporadic.M23 3 := by
  obtain ⟨r, hr, x, hsq, hcomm, hker⟩ := exists_of_permCheck m23Perm
    (σA := List.formPerm [0, 1] * List.formPerm [2, 3] * List.formPerm [6, 7] *
      List.formPerm [8, 9] * List.formPerm [12, 13] * List.formPerm [14, 15] *
      List.formPerm [18, 19] * List.formPerm [20, 21])
    (σB := List.formPerm [0, 15, 10, 2] * List.formPerm [1, 8, 20, 11] *
      List.formPerm [3, 4, 7, 22] * List.formPerm [5, 21, 13, 17] * List.formPerm [12, 19] *
      List.formPerm [14, 16])
    (by decide +kernel) (by decide +kernel) m23_permCheck
  have h4 : r = 4 := hr
  subst h4
  exact rankCertified_of_commuting_involutions x hsq hcomm hker (by norm_num)

theorem rankCertified_of_isSporadic_M23 {S : Type} [Group S]
    (h : NativeSporadic.IsSporadic S .M23) : RankCertified S 3 := by
  obtain ⟨e⟩ := h
  exact rankCertified_M23.of_mulEquiv e.symm

@[expose] def m12Words : Fin 4 → String :=
  ![
    "babaBabababaBaBabababaBabab",
    "babaBababaBabaBaBababaBababaB",
    "BababaBababaBaBabaBababaBabab",
    "baBababaBaBaBababaBabaBaBaBaBab"]

@[expose] def m12X (i : Fin 4) : NativeSporadic.M12 :=
  mathieuWord m12LocA m12LocB (m12Words i).toList

theorem rankCertified_M12 : RankCertified NativeSporadic.M12 3 := by
  refine rankCertified_of_central_section (t := m12LocA) (x := m12X) ?_ ?_ ?_ ?_ ?_ (by norm_num)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem rankCertified_of_isSporadic_M12 {S : Type} [Group S]
    (h : NativeSporadic.IsSporadic S .M12) : RankCertified S 3 := by
  obtain ⟨e⟩ := h
  exact rankCertified_M12.of_mulEquiv e.symm

end CFSG.GH74.E2
