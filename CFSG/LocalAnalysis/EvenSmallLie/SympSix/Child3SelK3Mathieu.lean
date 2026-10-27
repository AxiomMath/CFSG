module

public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3SelK3MathieuCheck
public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3SelK3SporSpec
public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3SelStar
public import CFSG.Sporadic.Mathieu.M22
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.Sporadic.Schreier.M23Base

public section

namespace CFSG.EvenSmallLie.Child3.SelK3

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open CFSG.Sporadic.Mathieu (m22gA m22gB m24gA m24gB card_M22 card_M24)

abbrev m23gA : Equiv.Perm (Fin 23) :=
  List.formPerm [0, 1] * List.formPerm [2, 3] * List.formPerm [6, 7] * List.formPerm [8, 9] *
    List.formPerm [12, 13] * List.formPerm [14, 15] * List.formPerm [18, 19] *
    List.formPerm [20, 21]

abbrev m23gB : Equiv.Perm (Fin 23) :=
  List.formPerm [0, 15, 10, 2] * List.formPerm [1, 8, 20, 11] * List.formPerm [3, 4, 7, 22] *
    List.formPerm [5, 21, 13, 17] * List.formPerm [12, 19] * List.formPerm [14, 16]

theorem rep_m22TA : Rep 22 m22TA m22gA := by
  unfold CFSG.Sporadic.Th.Rep
  decide

theorem rep_m22TB : Rep 22 m22TB m22gB := by
  unfold CFSG.Sporadic.Th.Rep
  decide

theorem rep_m23TA : Rep 23 m23TA m23gA := by
  unfold CFSG.Sporadic.Th.Rep
  decide

theorem rep_m23TB : Rep 23 m23TB m23gB := by
  unfold CFSG.Sporadic.Th.Rep
  decide

theorem rep_m24TA : Rep 24 m24TA m24gA := by
  unfold CFSG.Sporadic.Th.Rep
  decide

theorem rep_m24TB : Rep 24 m24TB m24gB := by
  unfold CFSG.Sporadic.Th.Rep
  decide

section M22

theorem k3_M22 : K3 CFSG.Blueprint.NativeSporadic.M22 :=
  k3_of_check (n := 22) (D := m22K3) rfl (by norm_num) (T := CFSG.Blueprint.NativeSporadic.M22)
    (gG := fun l => if l = 0 then m22gA else m22gB) (pair_gens rep_m22TA rep_m22TB
      (Subgroup.subset_closure (Set.mem_insert _ _))
      (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)))
    m22K3_check (a := 2) (m := 49280) (by rw [card_M22]; norm_num) (by norm_num) rfl

theorem excluded_M22 : ExcludedSource (CFSG.Blueprint.NativeSporadic.Carrier .M22) :=
  false_of_k3 k3_M22

end M22

section M23

theorem k3_M23 : K3 CFSG.Blueprint.NativeSporadic.M23 :=
  k3_of_check (n := 23) (D := m23K3) rfl (by norm_num) (T := CFSG.Blueprint.NativeSporadic.M23)
    (gG := fun l => if l = 0 then m23gA else m23gB) (pair_gens rep_m23TA rep_m23TB
      (Subgroup.subset_closure (Set.mem_insert _ _))
      (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)))
    m23K3_check (a := 2) (m := 1133440) (by rw [CFSG.Sporadic.Schreier.m23_card]; norm_num)
    (by norm_num) rfl

theorem excluded_M23 : ExcludedSource (CFSG.Blueprint.NativeSporadic.Carrier .M23) :=
  false_of_k3 k3_M23

end M23

section M24

theorem k3_M24 : K3 CFSG.Blueprint.NativeSporadic.M24 :=
  k3_of_check (n := 24) (D := m24K3) rfl (by norm_num) (T := CFSG.Blueprint.NativeSporadic.M24)
    (gG := fun l => if l = 0 then m24gA else m24gB) (pair_gens rep_m24TA rep_m24TB
      (Subgroup.subset_closure (Set.mem_insert _ _))
      (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)))
    m24K3_check (a := 3) (m := 9067520) (by rw [card_M24]; norm_num) (by norm_num) rfl

theorem excluded_M24 : ExcludedSource (CFSG.Blueprint.NativeSporadic.Carrier .M24) :=
  false_of_k3 k3_M24

end M24

end CFSG.EvenSmallLie.Child3.SelK3
