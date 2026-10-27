module

public import CFSG.GH74.Filter.Sporadic.PermSpec
public import CFSG.GH74.Uniqueness.SU.KI1r3FamSp2
public import Certificates.Data.CFSGNative.Filter.M24Data

public section

namespace CFSG.GH74.Filter

open CFSG.Blueprint CFSG.SectionRank CFSG.SectionRank.Native

theorem m24_permCheck : permCheck 24 m24Perm = true := by decide +kernel

theorem exists_E32_M24 :
    ∃ E : Subgroup CFSG.Blueprint.NativeSporadic.M24,
      CFSG.Open.IsElemAbelian 2 E ∧ Nat.card E = 32 := by
  let σA : Equiv.Perm (Fin 24) :=
    List.formPerm [0, 3] * List.formPerm [1, 6] * List.formPerm [2, 16] *
      List.formPerm [4, 12] * List.formPerm [5, 8] * List.formPerm [7, 14] *
      List.formPerm [9, 18] * List.formPerm [10, 17] * List.formPerm [11, 20] *
      List.formPerm [13, 15] * List.formPerm [19, 23] * List.formPerm [21, 22]
  let σB : Equiv.Perm (Fin 24) :=
    List.formPerm [0, 3, 5] * List.formPerm [1, 20, 13] * List.formPerm [2, 8, 14] *
      List.formPerm [4, 17, 9] * List.formPerm [12, 16, 15] * List.formPerm [18, 23, 22]
  change ∃ E : Subgroup (↥(Subgroup.closure {σA, σB})),
      CFSG.Open.IsElemAbelian 2 E ∧ Nat.card E = 32
  obtain ⟨r, hr, x, hsq, hcomm, hker⟩ :=
    CFSG.SectionRank.exists_of_permCheck m24Perm
      (σA := σA) (σB := σB)
      (by decide +kernel) (by decide +kernel) m24_permCheck
  have hlen : m24Perm.outs.length = 5 := by decide +kernel
  have hr5 : r = 5 := by rw [hr, hlen]
  subst r
  obtain ⟨E, hE, hc⟩ :=
    CFSG.GH74.Uniqueness.SU.K.R3.exists_isElemAbelian_of_commuting_involutions x
      (fun i => by simpa [sq] using hsq i)
      (fun i j => hcomm i j)
      hker
  refine ⟨E, hE, ?_⟩
  rw [hc, hlen]
  norm_num

theorem not_gen4_M24 : ¬ Gen4 NativeSporadic.M24 := by
  obtain ⟨E, hE, hc⟩ := exists_E32_M24
  exact not_gen4_of_elemAbelian E hE (by rw [hc]; norm_num)

end CFSG.GH74.Filter
