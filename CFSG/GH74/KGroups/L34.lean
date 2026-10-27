
module

public import CFSG.GH74.KGroups.L34Base

public import Mathlib
public import CFSG.GH74.KGroups.Generic
public import CFSG.GH74.KGroups.PermCheck
public import CFSG.GH74.KGroups.Checks
public import CFSG.GH74.KGroups.PSLN
public import CFSG.GH74.KGroups.FieldGF
public meta import CFSG.GH74.KGroups.Checks
public import CFSG.GH74.KGroups.L34Inputs
public meta import CFSG.GH74.KGroups.L34Inputs
public import Certificates.Certificate5122

public section

namespace CFSG.GH74.KGroups.L34

open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Blueprint Matrix

theorem QP21_valid :
    QP21.check = true ∧ QP21.orderCertificate = 20160 :=
  Certificates.certificate5122.1

theorem QP_valid :
    QP.check = true ∧ QP.orderCertificate = 20160 :=
  Certificates.certificate5122.2.1

theorem QP21_ok : ValidSchreier QP21 := QP21_valid.1

theorem QP_ok : ValidSchreier QP := QP_valid.1

theorem equiv_psl_P21 :
    Nonempty (Matrix.ProjectiveSpecialLinearGroup (Fin 3) GF4 ≃* QP21.originalSubgroup) := by
  refine PSLN.psl_equiv_closure (PSLN.ptEquivOf vec vec_ne vec_inj vec_surj) mA mB pa pb
    (PSLN.pointwise_of_exists vec vec_ne vec_inj vec_surj mA pa actA)
    (PSLN.pointwise_of_exists vec vec_ne vec_inj vec_surj mB pb actB) QP21.originalSubgroup
    QP21_closure ?_
  rw [card_group QP21 QP21_ok, QP21_valid.2, card_psl]

theorem blk :
    blockHom 21 21 (pa, pa') = PA ∧ blockHom 21 21 (pb, pb') = PB :=
  Certificates.certificate5122.2.2

theorem equiv_P21_P :
    Nonempty (QP21.originalSubgroup ≃* QP.originalSubgroup) := by
  have hpa : pa ∈ QP21.originalSubgroup := by
    rw [QP21_closure]; exact Subgroup.subset_closure (Set.mem_insert _ _)
  have hpb : pb ∈ QP21.originalSubgroup := by
    rw [QP21_closure]; exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  obtain ⟨φ, -⟩ := blockIso pa pb pa' pb' PA PB blk.1 blk.2 QP21.originalSubgroup
    QP.originalSubgroup QP21_closure QP_closure hpa hpb (by
      rw [card_group QP QP_ok, card_group QP21 QP21_ok, QP_valid.2, QP21_valid.2])
  exact ⟨φ⟩

theorem equiv_of_lieModel
    {K : Type} [Group K] (h : LieModel K .PSL 3 2 2) :
    Nonempty (K ≃* QP.originalSubgroup) := by
  have : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  obtain ⟨e1⟩ := PSLN.psl_equiv_of_lieModel (F := GF4) 3 2 2 (by norm_num) card_F h
  obtain ⟨e2⟩ := equiv_psl_P21
  obtain ⟨e3⟩ := equiv_P21_P
  exact ⟨e1.trans (e2.trans e3)⟩

end CFSG.GH74.KGroups.L34
