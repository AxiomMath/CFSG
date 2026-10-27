module

public import CFSG.GH74.GLS.C3.Layer2.L5A1
public meta import Mathlib.GroupTheory.SpecificGroups.Alternating
public meta import CFSG.GH74.GLS.C3.Prop121.ModelFive
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelDefs
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelEmb
public meta import CFSG.GH74.GLS.C3.Layer2.NumMoved
public meta import CFSG.GH74.GLS.C3.Layer2.L5Fin
public meta import CFSG.GH74.GLS.C3.Layer2.L5A1
public import Certificates.Certificate5045
public import Certificates.Certificate5046

public section

namespace CFSG.GH74.GLS.C3.Layer2.L5

open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2
  CFSG.GH74.GLS.C3.Layer2.Model

theorem T5_cent_R_le_chk : allT5.all (fun t => imp (decide (t ∉ Rml))
    (decide ((Rml.filter (fun r => decide (r * t = t * r))).length ≤ 4))) = true :=
  Certificates.certificate5046.1

theorem T5_cent_R_le
    {t : Amb 5} (ht : t ∈ T5) (htR : t ∉ Rm) :
    (Rml.filter (fun r => decide (r * t = t * r))).length ≤ 4 := by
  have h := T5_cent_R_le_chk
  simp only [List.all_eq_true, imp_eq_true, decide_eq_true_eq] at h
  exact h t (mem_allT5.2 ht) htR

theorem T5_cent_P_ne_chk : allT5.all (fun t => imp (decide (t ∉ Rml))
    (Pml.any fun p => decide (p ≠ 1 ∧ p * t = t * p))) = true :=
  Certificates.certificate5046.2.1

theorem T5_cent_P_ne
    {t : Amb 5} (ht : t ∈ T5) (htR : t ∉ Rm) :
    ∃ p ∈ Pm, p ≠ 1 ∧ p * t = t * p := by
  have h := T5_cent_P_ne_chk
  simp only [List.all_eq_true, imp_eq_true, List.any_eq_true, decide_eq_true_eq] at h
  obtain ⟨p, hp, hp1, hpt⟩ := h t (mem_allT5.2 ht) htR
  exact ⟨p, hp, hp1, hpt⟩

theorem wm_cycles_P_chk :
    Pml.all (fun p => imp (decide (p ≠ 1)) (Pml.all fun p' =>
    imp (decide (p' ≠ 1)) (decide (p' = p ∨ p' = wm * p * wm⁻¹ ∨
      p' = wm * (wm * p * wm⁻¹) * wm⁻¹)))) = true :=
  Certificates.certificate5046.2.2

theorem wm_cycles_P
    {p p' : Amb 5} (hp : p ∈ Pm) (hp1 : p ≠ 1) (hp' : p' ∈ Pm) (hp'1 : p' ≠ 1) :
    p' = p ∨ p' = wm * p * wm⁻¹ ∨ p' = wm * (wm * p * wm⁻¹) * wm⁻¹ := by
  have h := wm_cycles_P_chk
  simp only [List.all_eq_true, imp_eq_true, decide_eq_true_eq] at h
  exact h p hp hp1 p' hp' hp'1

end CFSG.GH74.GLS.C3.Layer2.L5
