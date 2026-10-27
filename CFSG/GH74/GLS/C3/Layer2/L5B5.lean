module

public import CFSG.GH74.GLS.C3.Layer2.L5B0
public meta import Mathlib.GroupTheory.SpecificGroups.Alternating
public meta import CFSG.GH74.GLS.C3.Prop121.ModelFive
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelDefs
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelEmb
public meta import CFSG.GH74.GLS.C3.Layer2.NumMoved
public meta import CFSG.GH74.GLS.C3.Layer2.L5Fin
public meta import CFSG.GH74.GLS.C3.Layer2.L5A1
public import CFSG.GH74.GLS.C3.Layer2.L5B5Inputs
public meta import CFSG.GH74.GLS.C3.Layer2.L5B5Inputs
public import Certificates.Certificate5045
public import Certificates.Certificate5050

public section

namespace CFSG.GH74.GLS.C3.Layer2.L5

open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2
  CFSG.GH74.GLS.C3.Layer2.Model

@[expose] def Mixm (z : Amb 5) : Prop := z ∈ Rm ∧ z ∉ Pm ∧ z ∉ Qm

theorem mixb_iff {z : Amb 5} : mixb z = true ↔ Mixm z := by
  simp [mixb, Mixm, mem_Rm, mem_Pm, mem_Qm, and_assoc]

instance :
    DecidablePred Mixm := fun z => decidable_of_iff (mixb z = true) mixb_iff

theorem T5_pow4_chk :
    allT5.all (fun t => decide (t * t * (t * t) = 1)) = true :=
  Certificates.certificate5050.1

theorem T5_pow4 {t : Amb 5} (ht : t ∈ T5) : t * t * (t * t) = 1 := by
  have h := T5_pow4_chk
  simp only [List.all_eq_true, decide_eq_true_eq] at h
  exact h t (mem_allT5.2 ht)

theorem T5_sq_mem_R_chk :
    allT5.all (fun t => decide (t * t ∈ Rml)) = true :=
  Certificates.certificate5050.2.1

theorem T5_sq_mem_R
    {t : Amb 5} (ht : t ∈ T5) : t * t ∈ Rm := by
  have h := T5_sq_mem_R_chk
  simp only [List.all_eq_true, decide_eq_true_eq] at h
  exact h t (mem_allT5.2 ht)

theorem T5_cent_Z_chk :
    allT5.all (fun z => imp (allT5.all fun t => decide (z * t = t * z))
    (decide (z ∈ ZTl))) = true :=
  Certificates.certificate5050.2.2.1

theorem T5_cent_Z
    {z : Amb 5} (hz : z ∈ T5) (hc : ∀ t ∈ T5, z * t = t * z) : z ∈ ZTl := by
  have h := T5_cent_Z_chk
  simp only [List.all_eq_true, imp_eq_true, decide_eq_true_eq] at h
  exact h z (mem_allT5.2 hz) (fun t ht => hc t (mem_allT5.1 ht))

theorem ZTl_P_chk :
    Pml.all (fun p => imp (decide (p ∈ ZTl)) (decide (p = 1 ∨ p = e1))) = true :=
  Certificates.certificate5050.2.2.2.2.1

theorem ZTl_P
    {p : Amb 5} (hp : p ∈ Pm) (hz : p ∈ ZTl) : p = 1 ∨ p = e1 := by
  have h := ZTl_P_chk
  simp only [List.all_eq_true, imp_eq_true, decide_eq_true_eq] at h
  exact h p hp hz

theorem e1_mem_Pm_check : e1 ∈ Pml :=
  Certificates.certificate5050.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem e1_mem_Pm : e1 ∈ Pm := by
  rw [mem_Pm]
  exact e1_mem_Pm_check

theorem f1_mem_Qm_check : f1 ∈ Qml :=
  Certificates.certificate5050.2.2.2.2.2.2.2.2.2.2.2.2.2.2

theorem f1_mem_Qm' : f1 ∈ Qm := by
  rw [mem_Qm]
  exact f1_mem_Qm_check

theorem T5_cent_invol_Z_chk :
    allT5.all (fun t => imp (decide (t * t ≠ 1))
    (allT5.all fun s => imp (decide (s * s = 1)) (imp (decide (s ≠ 1))
      (imp (decide (s * t = t * s)) (decide (s ∈ ZTl)))))) = true :=
  Certificates.certificate5050.2.2.2.2.2.2.2.1

theorem T5_cent_invol_Z
    {t : Amb 5} (ht : t ∈ T5) (ht2 : t * t ≠ 1) {s : Amb 5} (hs : s ∈ T5)
    (hs2 : s * s = 1) (hs1 : s ≠ 1) (hst : s * t = t * s) : s ∈ ZTl := by
  have h := T5_cent_invol_Z_chk
  simp only [List.all_eq_true, imp_eq_true, decide_eq_true_eq] at h
  exact h t (mem_allT5.2 ht) ht2 s (mem_allT5.2 hs) hs2 hs1 hst

theorem T5_JR_conj_chk :
    allT5.all (fun u => imp (decide (u * u = 1)) (imp (decide (u ∉ Rml))
    (allT5.all fun t => imp (decide (t * t = 1)) (imp (decide (t ∉ Rml))
      (Rml.any fun r => decide (r * u * r⁻¹ = t)))))) = true :=
  Certificates.certificate5050.2.2.2.2.2.2.2.2.1

theorem T5_JR_conj
    {u t : Amb 5} (hu : u ∈ T5) (hu2 : u * u = 1) (huR : u ∉ Rm) (ht : t ∈ T5)
    (ht2 : t * t = 1) (htR : t ∉ Rm) : ∃ r ∈ Rm, r * u * r⁻¹ = t := by
  have h := T5_JR_conj_chk
  simp only [List.all_eq_true, imp_eq_true, List.any_eq_true, decide_eq_true_eq] at h
  obtain ⟨r, hr, hrt⟩ := h u (mem_allT5.2 hu) hu2 huR t (mem_allT5.2 ht) ht2 htR
  exact ⟨r, hr, hrt⟩

theorem fz_chk :
    allT5.all (fun t1 => imp (decide (t1 * t1 = f1)) (allT5.all fun X =>
    imp (decide (X * X = 1)) (imp (!mixb X) (Rml.all fun V => imp (mixb V)
      (decide (t1 * X * t1⁻¹ ≠ X * V)))))) = true :=
  Certificates.certificate5050.2.2.2.2.2.2.2.2.2.2.2.1

theorem fz_model
    {t₁ : Amb 5} (ht : t₁ ∈ T5) (hsq : t₁ * t₁ = f1) {X : Amb 5} (hX : X ∈ T5)
    (hX2 : X * X = 1) (hXm : ¬ Mixm X) {V : Amb 5} (hV : Mixm V) : t₁ * X * t₁⁻¹ ≠ X * V := by
  have h := fz_chk
  simp only [List.all_eq_true, imp_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
  have h2 := h t₁ (mem_allT5.2 ht) hsq X (mem_allT5.2 hX) hX2
    (by simpa [← mixb_iff] using hXm) V (mem_Rm.1 hV.1) (mixb_iff.2 hV)
  exact h2

theorem four_F_chk :
    Rml.all (fun a => Rml.all fun b => Rml.all fun r =>
    imp (mixb a && mixb b && mixb (a * b) && decide (r ≠ 1) && !mixb r)
      (mixb (r * a) || mixb (r * b) || mixb (r * (a * b)))) = true :=
  Certificates.certificate5050.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem four_F
    {a b r : Amb 5} (ha : Mixm a) (hb : Mixm b) (hab : Mixm (a * b)) (hr : r ∈ Rm)
    (hr1 : r ≠ 1) (hrm : ¬ Mixm r) : Mixm (r * a) ∨ Mixm (r * b) ∨ Mixm (r * (a * b)) := by
  have h := four_F_chk
  simp only [List.all_eq_true, imp_eq_true, Bool.and_eq_true, Bool.or_eq_true,
    decide_eq_true_eq, Bool.not_eq_true'] at h
  have := h a (mem_Rm.1 ha.1) b (mem_Rm.1 hb.1) r (mem_Rm.1 hr)
    ⟨⟨⟨⟨mixb_iff.2 ha, mixb_iff.2 hb⟩, mixb_iff.2 hab⟩, hr1⟩, by simpa [← mixb_iff] using hrm⟩
  rcases this with (h1 | h1) | h1
  · exact Or.inl (mixb_iff.1 h1)
  · exact Or.inr (Or.inl (mixb_iff.1 h1))
  · exact Or.inr (Or.inr (mixb_iff.1 h1))

end CFSG.GH74.GLS.C3.Layer2.L5
