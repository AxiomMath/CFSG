
module

public import CFSG.GH74.GLS.C3.Layer2.L5C5cBase

public import CFSG.GH74.GLS.C3.Layer2.L5C5b
public meta import Mathlib.GroupTheory.SpecificGroups.Alternating
public meta import CFSG.GH74.GLS.C3.Prop121.ModelFive
public meta import CFSG.GH74.GLS.C3.Prop121.ModelFiveS
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelDefs
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelEmb
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelEnum
public meta import CFSG.GH74.GLS.C3.Layer2.NumMoved
public meta import CFSG.GH74.GLS.C3.Layer2.L5Fin
public meta import CFSG.GH74.GLS.C3.Layer2.L5A1
public meta import CFSG.GH74.GLS.C3.Layer2.L5B2
public meta import CFSG.GH74.GLS.C3.Layer2.L5C0
public meta import CFSG.GH74.GLS.C3.Layer2.L5C5b
public import CFSG.GH74.GLS.C3.Layer2.L5C5cInputs
public meta import CFSG.GH74.GLS.C3.Layer2.L5C5cInputs
public import CFSG.GH74.GLS.C3.Layer2.L5B2
public import CFSG.GH74.GLS.C3.Layer2.FinModelEnum
public import CFSG.GH74.GLS.C3.Layer2.L5C0Inputs
public import CFSG.GH74.GLS.C3.Layer2.L5C5a
public import CFSG.GH74.GLS.C3.Layer2.L5C0
public import CFSG.GH74.GLS.C3.Layer2.L5C5bInputs
public import Certificates.Certificate5066

public section

namespace CFSG.GH74.GLS.C3.Layer2.L5

open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2
  CFSG.GH74.GLS.C3.Layer2.Model

theorem conjI_lt
    {h a : Nat} (hh : h < 128) (ha : a < 128) : conjI h a < 128 :=
  mt0_lt (mt0_lt hh ha) (inv0_lt hh)

theorem dec0_conjI
    {h a : Nat} (hh : h < 128) (ha : a < 128) :
    dec0 (conjI h a) = dec0 h * dec0 a * (dec0 h)⁻¹ := by
  unfold conjI
  rw [dec0_mul (mt0_lt hh ha) (inv0_lt hh), dec0_mul hh ha, dec0_inv hh]

theorem wdChk_true : wdChk = true :=
  Certificates.certificate5066.1

theorem gI_lt (k : Nat) : gI.getD k 0 < 128 := by
  have h := wdChk_true
  simp only [wdChk, Bool.and_eq_true] at h
  exact getD_lt_of_all h.1 k

theorem Wd_eval
    {i : Nat} (hi : i < 128) : evI gI (Wd.getD i []) = i := by
  have h := wdChk_true
  simp only [wdChk, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  exact (h.2 i hi).1

theorem relsChk_true : relsChk = true :=
  Certificates.certificate5066.2.1

theorem rels_eval : ∀ r ∈ relsL, evI gI r.1 = evI gI r.2 := by
  have h := relsChk_true
  simp only [relsChk, List.all_eq_true, decide_eq_true_eq] at h
  exact h

theorem gamChk_true :
    (List.range 4).all gamChk = true :=
  Certificates.certificate5066.2.2

theorem gamChk_m {m : Nat} (hm : m < 4) : gamChk m = true := by
  have h := gamChk_true
  simp only [List.all_eq_true, List.mem_range] at h
  exact h m hm

theorem gam_facts {m : Nat} (hm : m < 4) :
    ssData.getD m 0 < 128 ∧
    (∀ a < 128, (gamTabs.getD m #[]).getD a 0 < 128 ∧ (gamInvTabs.getD m #[]).getD a 0 < 128 ∧
      (gamInvTabs.getD m #[]).getD ((gamTabs.getD m #[]).getD a 0) 0 = a ∧
      (gamTabs.getD m #[]).getD ((gamInvTabs.getD m #[]).getD a 0) 0 = a) ∧
    (∀ a < 128, ∀ b < 128, (gamTabs.getD m #[]).getD (mt0.getD (a * 128 + b) 0) 0 =
      mt0.getD ((gamTabs.getD m #[]).getD a 0 * 128 + (gamTabs.getD m #[]).getD b 0) 0) ∧
    (gamTabs.getD m #[]).getD (ssData.getD m 0) 0 = ssData.getD m 0 ∧
    (∀ a < 128, (gamTabs.getD m #[]).getD ((gamTabs.getD m #[]).getD a 0) 0 =
      conjI (ssData.getD m 0) a) := by
  have h := gamChk_m hm
  simp only [gamChk, Bool.and_eq_true, List.all_eq_true, List.mem_range,
    decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hs, hbij⟩, hmul⟩, hfix⟩, hsq⟩ := h
  refine ⟨hs, fun a ha => ?_, hmul, hfix, hsq⟩
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hbij a ha
  exact ⟨h1, h2, h3, h4⟩

@[expose] def gam
    (m : Fin 4) : ↥Sh0 ≃* ↥Sh0 where
  toFun h := dec0 ((gamTabs.getD m.val #[]).getD (idx0 (h : Perm (Fin 16))) 0)
  invFun h := dec0 ((gamInvTabs.getD m.val #[]).getD (idx0 (h : Perm (Fin 16))) 0)
  left_inv h := by
    obtain ⟨a, ha, rfl⟩ := dec0_surj h
    obtain ⟨h1, h2, h3, h4⟩ := (gam_facts m.2).2.1 a ha
    show dec0 ((gamInvTabs.getD m.val #[]).getD (idx0 (dec0
      ((gamTabs.getD m.val #[]).getD (idx0 (dec0 a : Perm (Fin 16))) 0) : Perm (Fin 16))) 0) =
        dec0 a
    rw [idx0_dec0 ha, idx0_dec0 h1, h3]
  right_inv h := by
    obtain ⟨a, ha, rfl⟩ := dec0_surj h
    obtain ⟨h1, h2, h3, h4⟩ := (gam_facts m.2).2.1 a ha
    show dec0 ((gamTabs.getD m.val #[]).getD (idx0 (dec0
      ((gamInvTabs.getD m.val #[]).getD (idx0 (dec0 a : Perm (Fin 16))) 0) : Perm (Fin 16))) 0) =
        dec0 a
    rw [idx0_dec0 ha, idx0_dec0 h2, h4]
  map_mul' a b := by
    obtain ⟨i, hi, rfl⟩ := dec0_surj a
    obtain ⟨j, hj, rfl⟩ := dec0_surj b
    obtain ⟨hsa, -, hmul, -, -⟩ := gam_facts m.2
    obtain ⟨hi1, -, -, -⟩ := (gam_facts m.2).2.1 i hi
    obtain ⟨hj1, -, -, -⟩ := (gam_facts m.2).2.1 j hj
    show dec0 ((gamTabs.getD m.val #[]).getD (idx0 ((dec0 i * dec0 j : ↥Sh0) : Perm (Fin 16))) 0) =
      dec0 ((gamTabs.getD m.val #[]).getD (idx0 (dec0 i : Perm (Fin 16))) 0) *
        dec0 ((gamTabs.getD m.val #[]).getD (idx0 (dec0 j : Perm (Fin 16))) 0)
    rw [← dec0_mul hi hj, idx0_dec0 (mt0_lt hi hj), idx0_dec0 hi, idx0_dec0 hj,
      ← dec0_mul hi1 hj1, hmul i hi j hj]

theorem gam_dec0
    (m : Fin 4) {i : Nat} (hi : i < 128) :
    gam m (dec0 i) = dec0 ((gamTabs.getD m.val #[]).getD i 0) := by
  show dec0 ((gamTabs.getD m.val #[]).getD (idx0 (dec0 i : Perm (Fin 16))) 0) = _
  rw [idx0_dec0 hi]

@[expose] def ext2Data
    (m : Fin 4) : Ext2Data ↥Sh0 where
  α := gam m
  u := dec0 (ssData.getD m.val 0)
  sq h := by
    obtain ⟨a, ha, rfl⟩ := dec0_surj h
    obtain ⟨hs, hbij, -, -, hsq⟩ := gam_facts m.2
    obtain ⟨ha1, -, -, -⟩ := hbij a ha
    rw [gam_dec0 m ha, gam_dec0 m ha1, hsq a ha, dec0_conjI hs ha]
  fix := by
    obtain ⟨hs, -, -, hfix, -⟩ := gam_facts m.2
    rw [gam_dec0 m hs, hfix]

abbrev Sh2
    (m : Fin 4) : Type := Ext2 (ext2Data m)

@[expose] def inc
    (m : Fin 4) : ↥Sh0 →* Sh2 m := Ext2.inc

theorem mem_range_inc
    (m : Fin 4) {a : Sh2 m} : a ∈ (inc m).range ↔ a.snd = false :=
  Ext2.mem_range_inc

end CFSG.GH74.GLS.C3.Layer2.L5
