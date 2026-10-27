module

public import CFSG.CGT.Timmesfeld75.ListWCPermSound
public import CFSG.CGT.Timmesfeld75.ListWCMathieuData
public import CFSG.CGT.Timmesfeld75.ListWCAssembly
public import CFSG.Sporadic.Mathieu.M22
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.Sporadic.Schreier.M23Base

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Blueprint CFSG.Sporadic.Th CFSG.Sporadic.Th.Native WCCheck

@[expose] def M22WCCheck : Prop := wcCheck m22Data = true

@[expose] def M23WCCheck : Prop := wcCheck m23Data = true

@[expose] def M24WCCheck : Prop := wcCheck m24Data = true

section M22

noncomputable def m22gen (l : ℤ) : NativeSporadic.M22 :=
  if l = 1 then CFSG.Sporadic.Mathieu.m22a else if l = -1 then CFSG.Sporadic.Mathieu.m22a⁻¹ else
    if l = 2 then CFSG.Sporadic.Mathieu.m22b else
      if l = -2 then CFSG.Sporadic.Mathieu.m22b⁻¹ else 1

theorem rep_m22gen (l : ℤ) : CFSG.Sporadic.Th.Rep 22 (m22gens l) (m22gen l) := by
  unfold m22gens m22gen
  split_ifs
  · unfold CFSG.Sporadic.Th.Rep
    decide
  · unfold CFSG.Sporadic.Th.Rep
    decide
  · unfold CFSG.Sporadic.Th.Rep
    decide
  · unfold CFSG.Sporadic.Th.Rep
    decide
  · exact Rep.idT (by norm_num)

theorem m22gen_neg (l : ℤ) : m22gen (-l) = (m22gen l)⁻¹ := by
  unfold m22gen
  split_ifs <;> first | omega | simp_all

theorem wcOrderConj_m22 (h : M22WCCheck) :
    WCOrderConj NativeSporadic.M22 16 :=
  wcOrderConj_of_wcCheck (D := m22Data) (M := NativeSporadic.M22) (by norm_num [m22Data])
    rep_m22gen m22gen_neg ⟨3465, by decide, by
      rw [show 2 ^ m22Data.pc.length * 3465 = 443520 from rfl]
      exact CFSG.Sporadic.Mathieu.card_M22⟩ h

end M22

section M23

noncomputable abbrev m23a : NativeSporadic.M23 :=
  ⟨List.formPerm [0, 1] * List.formPerm [2, 3] * List.formPerm [6, 7] * List.formPerm [8, 9] *
    List.formPerm [12, 13] * List.formPerm [14, 15] * List.formPerm [18, 19] *
    List.formPerm [20, 21], Subgroup.subset_closure (Set.mem_insert _ _)⟩

noncomputable abbrev m23b : NativeSporadic.M23 :=
  ⟨List.formPerm [0, 15, 10, 2] * List.formPerm [1, 8, 20, 11] * List.formPerm [3, 4, 7, 22] *
    List.formPerm [5, 21, 13, 17] * List.formPerm [12, 19] * List.formPerm [14, 16],
    Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)⟩

noncomputable def m23gen (l : ℤ) : NativeSporadic.M23 :=
  if l = 1 then m23a else if l = -1 then m23a⁻¹ else if l = 2 then m23b else
    if l = -2 then m23b⁻¹ else 1

theorem rep_m23gen (l : ℤ) : CFSG.Sporadic.Th.Rep 23 (m23gens l) (m23gen l) := by
  unfold m23gens m23gen
  split_ifs
  · unfold CFSG.Sporadic.Th.Rep
    decide
  · unfold CFSG.Sporadic.Th.Rep
    decide
  · unfold CFSG.Sporadic.Th.Rep
    decide
  · unfold CFSG.Sporadic.Th.Rep
    decide
  · exact Rep.idT (by norm_num)

theorem m23gen_neg (l : ℤ) : m23gen (-l) = (m23gen l)⁻¹ := by
  unfold m23gen
  split_ifs <;> first | omega | simp_all

theorem wcOrderConj_m23 (h : M23WCCheck) :
    WCOrderConj NativeSporadic.M23 16 :=
  wcOrderConj_of_wcCheck (D := m23Data) (M := NativeSporadic.M23) (by norm_num [m23Data])
    rep_m23gen m23gen_neg ⟨79695, by decide, by
      rw [show 2 ^ m23Data.pc.length * 79695 = 10200960 from rfl]
      exact CFSG.Sporadic.Schreier.m23_card⟩ h

end M23

section M24

noncomputable def m24gen (l : ℤ) : NativeSporadic.M24 :=
  if l = 1 then CFSG.Sporadic.Mathieu.m24a else if l = -1 then CFSG.Sporadic.Mathieu.m24a⁻¹ else
    if l = 2 then CFSG.Sporadic.Mathieu.m24b else
      if l = -2 then CFSG.Sporadic.Mathieu.m24b⁻¹ else 1

theorem rep_m24gen (l : ℤ) : CFSG.Sporadic.Th.Rep 24 (m24gens l) (m24gen l) := by
  unfold m24gens m24gen
  split_ifs
  · unfold CFSG.Sporadic.Th.Rep
    decide
  · unfold CFSG.Sporadic.Th.Rep
    decide
  · unfold CFSG.Sporadic.Th.Rep
    decide
  · unfold CFSG.Sporadic.Th.Rep
    decide
  · exact Rep.idT (by norm_num)

theorem m24gen_neg (l : ℤ) : m24gen (-l) = (m24gen l)⁻¹ := by
  unfold m24gen
  split_ifs <;> first | omega | simp_all

theorem wcOrderConj_m24 (h : M24WCCheck) :
    WCOrderConj NativeSporadic.M24 16 :=
  wcOrderConj_of_wcCheck (D := m24Data) (M := NativeSporadic.M24) (by norm_num [m24Data])
    rep_m24gen m24gen_neg ⟨239085, by decide, by
      rw [show 2 ^ m24Data.pc.length * 239085 = 244823040 from rfl]
      exact CFSG.Sporadic.Mathieu.card_M24⟩ h

end M24

theorem listWCIdentification
    (h22 : M22WCCheck)
    (h23 : M23WCCheck) (h24 : M24WCCheck) : ListWCIdentification :=
  listWCIdentification_of_mathieu ⟨wcOrderConj_m22 h22, wcOrderConj_m23 h23, wcOrderConj_m24 h24⟩

end CFSG.CGT.Timmesfeld75
