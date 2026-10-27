
module

public import CFSG.GH74.GLS.C3.Layer2.L5A1Base

public import CFSG.GH74.GLS.C3.Layer2.L5Fin
public meta import Mathlib.GroupTheory.SpecificGroups.Alternating
public meta import CFSG.GH74.GLS.C3.Prop121.ModelFive
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelDefs
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelEmb
public meta import CFSG.GH74.GLS.C3.Layer2.NumMoved
public meta import CFSG.GH74.GLS.C3.Layer2.L5Fin
public import CFSG.GH74.GLS.C3.Layer2.L5A1Inputs
public meta import CFSG.GH74.GLS.C3.Layer2.L5A1Inputs
public import Certificates.Certificate5045

public section

namespace CFSG.GH74.GLS.C3.Layer2.L5

open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2
  CFSG.GH74.GLS.C3.Layer2.Model

theorem Pml_mul_chk : mulClosedChk Pml = true :=
  Certificates.certificate5045.1

theorem Pml_inv_chk : invClosedChk Pml = true :=
  Certificates.certificate5045.2.1

theorem Qml_mul_chk : mulClosedChk Qml = true :=
  Certificates.certificate5045.2.2.1

theorem Qml_inv_chk : invClosedChk Qml = true :=
  Certificates.certificate5045.2.2.2.1

theorem Rml_mul_chk : mulClosedChk Rml = true :=
  Certificates.certificate5045.2.2.2.2.1

theorem Rml_inv_chk : invClosedChk Rml = true :=
  Certificates.certificate5045.2.2.2.2.2.1

theorem one_mem_Rml : (1 : Amb 5) ∈ Rml :=
  Certificates.certificate5045.2.2.2.2.2.2.1

@[expose] def Pm : Subgroup (Amb 5) :=
  lsub Pml one_mem_Pml (mul_of_chk Pml_mul_chk) (inv_of_chk Pml_inv_chk)

@[expose] def Qm : Subgroup (Amb 5) :=
  lsub Qml one_mem_Qml (mul_of_chk Qml_mul_chk) (inv_of_chk Qml_inv_chk)

@[expose] def Rm : Subgroup (Amb 5) :=
  lsub Rml one_mem_Rml (mul_of_chk Rml_mul_chk) (inv_of_chk Rml_inv_chk)

theorem mem_Pm {p : Amb 5} : p ∈ Pm ↔ p ∈ Pml := Iff.rfl

theorem mem_Qm {p : Amb 5} : p ∈ Qm ↔ p ∈ Qml := Iff.rfl

theorem mem_Rm {p : Amb 5} : p ∈ Rm ↔ p ∈ Rml := Iff.rfl

theorem Pml_nodup : Pml.Nodup :=
  Certificates.certificate5045.2.2.2.2.2.2.2.1

theorem Qml_nodup : Qml.Nodup :=
  Certificates.certificate5045.2.2.2.2.2.2.2.2.1

theorem Rml_nodup : Rml.Nodup :=
  Certificates.certificate5045.2.2.2.2.2.2.2.2.2.1

theorem card_Pm : Nat.card Pm = 4 := by
  rw [natCard_eq_length Pm Pml Pml_nodup (fun p => Iff.rfl)]
  rfl

theorem card_Qm : Nat.card Qm = 4 := by
  rw [natCard_eq_length Qm Qml Qml_nodup (fun p => Iff.rfl)]
  rfl

theorem card_Rm : Nat.card Rm = 16 := by
  rw [natCard_eq_length Rm Rml Rml_nodup (fun p => Iff.rfl)]
  rfl

theorem Pml_sub_chk :
    Pml.all (fun p => decide (p ∈ Rml)) = true :=
  Certificates.certificate5045.2.2.2.2.2.2.2.2.2.2.1

theorem Qml_sub_chk :
    Qml.all (fun p => decide (p ∈ Rml)) = true :=
  Certificates.certificate5045.2.2.2.2.2.2.2.2.2.2.2.1

theorem Pm_le_Rm : Pm ≤ Rm := fun p hp => by
  have h := Pml_sub_chk
  simp only [List.all_eq_true, decide_eq_true_eq] at h
  exact h p hp

theorem Qm_le_Rm : Qm ≤ Rm := fun p hp => by
  have h := Qml_sub_chk
  simp only [List.all_eq_true, decide_eq_true_eq] at h
  exact h p hp

theorem Rml_prod_chk :
    Rml.all (fun r => Pml.any fun p => Qml.any fun q => decide (r = p * q)) =
    true :=
  Certificates.certificate5045.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem Rm_eq_sup : Pm ⊔ Qm = Rm := by
  apply le_antisymm (sup_le Pm_le_Rm Qm_le_Rm)
  intro r hr
  have h := Rml_prod_chk
  simp only [List.all_eq_true, List.any_eq_true, decide_eq_true_eq] at h
  obtain ⟨p, hp, q, hq, rfl⟩ := h r hr
  exact mul_mem (mem_sup_left hp) (mem_sup_right hq)

theorem Pml_Qml_chk :
    Pml.all (fun p => imp (decide (p ∈ Qml)) (decide (p = 1))) = true :=
  Certificates.certificate5045.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem Pm_inf_Qm : Pm ⊓ Qm = ⊥ := by
  rw [eq_bot_iff]
  rintro p ⟨hP, hQ⟩
  have h := Pml_Qml_chk
  simp only [List.all_eq_true, imp_eq_true, decide_eq_true_eq] at h
  exact Subgroup.mem_bot.2 (h p hP hQ)

theorem Rml_comm_chk :
    Rml.all (fun a => Rml.all fun b => decide (a * b = b * a)) = true :=
  Certificates.certificate5045.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem Rm_comm : ∀ a ∈ Rm, ∀ b ∈ Rm, a * b = b * a := by
  have h := Rml_comm_chk
  simp only [List.all_eq_true, decide_eq_true_eq] at h
  exact fun a ha b hb => h a ha b hb

theorem Rml_sq_chk :
    Rml.all (fun a => decide (a * a = 1)) = true :=
  Certificates.certificate5045.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem Rm_sq : ∀ a ∈ Rm, a * a = 1 := by
  have h := Rml_sq_chk
  simp only [List.all_eq_true, decide_eq_true_eq] at h
  exact fun a ha => h a ha

theorem PQ_comm : ∀ p ∈ Pm, ∀ q ∈ Qm, p * q = q * p :=
  fun p hp q hq => Rm_comm p (Pm_le_Rm hp) q (Qm_le_Rm hq)

theorem Rml_T5_chk : Rml.all T5b = true :=
  Certificates.certificate5045.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem Rm_le_T5 : Rm ≤ T5 := fun p hp => by
  have h := Rml_T5_chk
  simp only [List.all_eq_true] at h
  exact mem_T5_of_b (h p hp)

theorem Pm_le_T5 : Pm ≤ T5 := Pm_le_Rm.trans Rm_le_T5

theorem Qm_le_T5 : Qm ≤ T5 := Qm_le_Rm.trans Rm_le_T5

theorem wm_mem_Km : wm ∈ Km :=
  Certificates.certificate5045.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem wm_cube : wm * wm * wm = 1 :=
  Certificates.certificate5045.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem wm_ne_one : wm ≠ 1 :=
  Certificates.certificate5045.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem wm_comm_Q_chk :
    Qml.all (fun q => decide (wm * q = q * wm)) = true :=
  Certificates.certificate5045.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem wm_comm_Q : ∀ q ∈ Qm, wm * q = q * wm := by
  have h := wm_comm_Q_chk
  simp only [List.all_eq_true, decide_eq_true_eq] at h
  exact fun q hq => h q hq

theorem wm_norm_P_chk :
    Pml.all (fun p => decide (wm * p * wm⁻¹ ∈ Pml)) = true :=
  Certificates.certificate5045.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem wm_norm_P : ∀ p ∈ Pm, wm * p * wm⁻¹ ∈ Pm := by
  have h := wm_norm_P_chk
  simp only [List.all_eq_true, decide_eq_true_eq] at h
  exact fun p hp => h p hp

theorem wm_free_chk :
    Pml.all (fun p => imp (decide (p ≠ 1)) (decide (wm * p * wm⁻¹ ≠ p))) = true :=
  Certificates.certificate5045.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem wm_free : ∀ p ∈ Pm, p ≠ 1 → wm * p * wm⁻¹ ≠ p := by
  have h := wm_free_chk
  simp only [List.all_eq_true, imp_eq_true, decide_eq_true_eq] at h
  exact fun p hp hp1 => h p hp hp1

theorem wm_norm_R_chk :
    Rml.all (fun r => decide (wm * r * wm⁻¹ ∈ Rml)) = true :=
  Certificates.certificate5045.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem wm_norm_R : ∀ r ∈ Rm, wm * r * wm⁻¹ ∈ Rm := by
  have h := wm_norm_R_chk
  simp only [List.all_eq_true, decide_eq_true_eq] at h
  exact fun r hr => h r hr

theorem Qm_coord_chk :
    allT5.all (fun g => decide (g.1 = 1 ↔ g ∈ Qml)) = true :=
  Certificates.certificate5045.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem Qm_coord {g : Amb 5} (hg : g ∈ T5) : g.1 = 1 ↔ g ∈ Qm := by
  have h := Qm_coord_chk
  simp only [List.all_eq_true, decide_eq_true_eq] at h
  exact h g (mem_allT5.2 hg)

theorem Pm_coord_chk :
    allT5.all (fun g => decide (g.2 = 1 ↔ g ∈ Pml)) = true :=
  Certificates.certificate5045.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem Pm_coord {g : Amb 5} (hg : g ∈ T5) : g.2 = 1 ↔ g ∈ Pm := by
  have h := Pm_coord_chk
  simp only [List.all_eq_true, decide_eq_true_eq] at h
  exact h g (mem_allT5.2 hg)

theorem T5_inf_Km : T5 ⊓ Km = Pm := by
  ext g
  rw [Subgroup.mem_inf]
  constructor
  · rintro ⟨hT, hK⟩
    exact (Pm_coord hT).1 (mem_Km.1 hK).1
  · intro hP
    refine ⟨Pm_le_T5 hP, ?_⟩
    rw [mem_Km]
    refine ⟨(Pm_coord (Pm_le_T5 hP)).2 hP, ?_⟩
    exact T5_sign_of_snd (Pm_le_T5 hP) ((Pm_coord (Pm_le_T5 hP)).2 hP)

theorem FIN1_chk :
    Rml.all (fun u => Rml.all fun v => imp (decide (u ≠ 1)) (imp (decide (v ≠ 1))
    (imp (decide (u ≠ v)) (imp (decide (wm * u * wm⁻¹ ∈ [u, v, u * v] ∧
      wm * v * wm⁻¹ ∈ [u, v, u * v])) (decide ((u ∈ Pml ∧ v ∈ Pml) ∨ (u ∈ Qml ∧ v ∈ Qml))))))) =
    true :=
  Certificates.certificate5045.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem FIN1
    {u v : Amb 5} (hu : u ∈ Rm) (hv : v ∈ Rm) (hu1 : u ≠ 1) (hv1 : v ≠ 1) (huv : u ≠ v)
    (hwu : wm * u * wm⁻¹ ∈ [u, v, u * v]) (hwv : wm * v * wm⁻¹ ∈ [u, v, u * v]) :
    (u ∈ Pm ∧ v ∈ Pm) ∨ (u ∈ Qm ∧ v ∈ Qm) := by
  have h := FIN1_chk
  simp only [List.all_eq_true, imp_eq_true, decide_eq_true_eq] at h
  exact h u hu v hv hu1 hv1 huv ⟨hwu, hwv⟩

theorem FIN2_chk :
    Rml.all (fun u => Rml.all fun v => imp (decide (u ≠ 1)) (imp (decide (v ≠ 1))
    (imp (decide (u ≠ v)) (imp (decide (u ∉ Qml ∧ v ∉ Qml ∧ u * v ∉ Qml))
      (imp (decide (u ∈ Pml ∨ v ∈ Pml ∨ u * v ∈ Pml))
        (decide (wm * u * wm⁻¹ ∈ [u, v, u * v] ∨ wm * v * wm⁻¹ ∈ [u, v, u * v] ∨
          wm * (u * v) * wm⁻¹ ∈ [u, v, u * v]))))))) = true :=
  Certificates.certificate5045.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem FIN2
    {u v : Amb 5} (hu : u ∈ Rm) (hv : v ∈ Rm) (hu1 : u ≠ 1) (hv1 : v ≠ 1) (huv : u ≠ v)
    (hQ : u ∉ Qm ∧ v ∉ Qm ∧ u * v ∉ Qm) (hP : u ∈ Pm ∨ v ∈ Pm ∨ u * v ∈ Pm) :
    wm * u * wm⁻¹ ∈ [u, v, u * v] ∨ wm * v * wm⁻¹ ∈ [u, v, u * v] ∨
      wm * (u * v) * wm⁻¹ ∈ [u, v, u * v] := by
  have h := FIN2_chk
  simp only [List.all_eq_true, imp_eq_true, decide_eq_true_eq] at h
  exact h u hu v hv hu1 hv1 huv hQ hP

theorem centRm_chk :
    F5list.all (fun g => imp (Rml.all fun r => decide (g * r = r * g))
    (decide (g ∈ Rml))) = true :=
  Certificates.certificate5045.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem centRm
    {g : Amb 5} (hg : g ∈ Fgrp 5) (hc : ∀ r ∈ Rm, g * r = r * g) : g ∈ Rm := by
  have h := centRm_chk
  simp only [List.all_eq_true, imp_eq_true, decide_eq_true_eq] at h
  exact h g (mem_F5list.2 hg) (fun r hr => hc r hr)

theorem T5_cent_le_chk : allT5.all (fun t => imp (decide (t ∉ Rml))
    (decide ((allT5.filter (fun s => decide (s * t = t * s))).length ≤ 8))) = true :=
  Certificates.certificate5045.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem T5_cent_le {t : Amb 5} (ht : t ∈ T5) (htR : t ∉ Rm) :
    (allT5.filter (fun s => decide (s * t = t * s))).length ≤ 8 := by
  have h := T5_cent_le_chk
  simp only [List.all_eq_true, imp_eq_true, decide_eq_true_eq] at h
  exact h t (mem_allT5.2 ht) htR

theorem Rm_prod : ∀ r ∈ Rm, ∃ p ∈ Pm, ∃ q ∈ Qm, r = p * q := by
  have h := Rml_prod_chk
  simp only [List.all_eq_true, List.any_eq_true, decide_eq_true_eq] at h
  exact fun r hr => h r hr

theorem T5_norm_Rm_chk :
    allT5.all (fun t => Rml.all fun r => decide (t * r * t⁻¹ ∈ Rml)) =
    true :=
  Certificates.certificate5045.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem T5_norm_Rm
    {t : Amb 5} (ht : t ∈ T5) {r : Amb 5} (hr : r ∈ Rm) : t * r * t⁻¹ ∈ Rm := by
  have h := T5_norm_Rm_chk
  simp only [List.all_eq_true, decide_eq_true_eq] at h
  exact h t (mem_allT5.2 ht) r hr

theorem Rm_inf_Km : Rm ⊓ Km = Pm := by
  ext g
  rw [Subgroup.mem_inf]
  constructor
  · rintro ⟨hR, hK⟩
    rw [← T5_inf_Km]
    exact ⟨Rm_le_T5 hR, hK⟩
  · intro hP
    refine ⟨Pm_le_Rm hP, ?_⟩
    have : g ∈ T5 ⊓ Km := T5_inf_Km ▸ hP
    exact this.2

theorem V4_cent_chk :
    (g5Perms 4).all (fun τ => imp (decide (τ * x4 = x4 * τ))
    (imp (decide (τ * y4 = y4 * τ)) (decide (τ ∈ V4l)))) = true :=
  Certificates.certificate5045.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem V4_cent
    {τ : Perm (Fin 4)} (h1 : τ * x4 = x4 * τ) (h2 : τ * y4 = y4 * τ) : τ ∈ V4l := by
  have h := V4_cent_chk
  simp only [List.all_eq_true, imp_eq_true, decide_eq_true_eq] at h
  exact h τ (mem_g5Perms 4 τ) h1 h2

theorem V4_even_chk :
    V4l.all (fun τ => decide (sign τ = 1)) = true :=
  Certificates.certificate5045.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

theorem V4_even {τ : Perm (Fin 4)} (h : τ ∈ V4l) : sign τ = 1 := by
  have h' := V4_even_chk
  simp only [List.all_eq_true, decide_eq_true_eq] at h'
  exact h' τ h

theorem f1_mem_Qm : f1 ∈ Qm := by simp [mem_Qm, Qml]

theorem f2_mem_Qm : f2 ∈ Qm := by simp [mem_Qm, Qml]

theorem Pm_le_Fgrp : Pm ≤ Fgrp 5 := Pm_le_T5.trans T5_le_Fgrp

theorem Qm_le_Fgrp : Qm ≤ Fgrp 5 := Qm_le_T5.trans T5_le_Fgrp

theorem Rm_le_Fgrp : Rm ≤ Fgrp 5 := Rm_le_T5.trans T5_le_Fgrp

end CFSG.GH74.GLS.C3.Layer2.L5
