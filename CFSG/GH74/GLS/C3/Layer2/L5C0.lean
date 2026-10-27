
module

public import CFSG.GH74.GLS.C3.Layer2.L5C0Base

public import CFSG.GH74.GLS.C3.Layer2.L5B2
public import CFSG.GH74.GLS.C3.Layer2.FinModelEnum
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
public import CFSG.GH74.GLS.C3.Layer2.L5C0Inputs
public meta import CFSG.GH74.GLS.C3.Layer2.L5C0Inputs
public import CFSG.GH74.GLS.C3.Layer2.L5Fin
public import CFSG.GH74.GLS.C3.Layer2.L5A1Inputs
public import Certificates.Certificate5051

public section

namespace CFSG.GH74.GLS.C3.Layer2.L5

open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2
  CFSG.GH74.GLS.C3.Layer2.Model

theorem el16_mem_chk :
    (List.finRange 16).all (fun i => decide (el16 i ∈ Rml)) = true :=
  Certificates.certificate5051.1

theorem el16_mem
    (i : Fin 16) : el16 i ∈ Rm := by
  have h := el16_mem_chk
  simp only [List.all_eq_true, List.mem_finRange, decide_eq_true_eq] at h
  exact mem_Rm.2 (h i trivial)

theorem idx16_el16_chk :
    (List.finRange 16).all (fun i => decide (idx16 (el16 i) = i)) = true :=
  Certificates.certificate5051.2.1

theorem idx16_el16 (i : Fin 16) : idx16 (el16 i) = i := by
  have h := idx16_el16_chk
  simp only [List.all_eq_true, List.mem_finRange, decide_eq_true_eq] at h
  exact h i trivial

theorem el16_idx16_chk :
    Rml.all (fun r => decide (el16 (idx16 r) = r)) = true :=
  Certificates.certificate5051.2.2.1

theorem el16_idx16
    {r : Amb 5} (hr : r ∈ Rm) : el16 (idx16 r) = r := by
  have h := el16_idx16_chk
  simp only [List.all_eq_true, decide_eq_true_eq] at h
  exact h r (mem_Rm.1 hr)

theorem el16_xor_chk :
    (List.finRange 16).all (fun i => (List.finRange 16).all fun j =>
    decide (el16 (xor16 i j) = el16 i * el16 j)) = true :=
  Certificates.certificate5051.2.2.2.1

theorem el16_xor
    (i j : Fin 16) : el16 (xor16 i j) = el16 i * el16 j := by
  have h := el16_xor_chk
  simp only [List.all_eq_true, List.mem_finRange, decide_eq_true_eq] at h
  exact h i trivial j trivial

theorem idx16_mul
    {r s : Amb 5} (hr : r ∈ Rm) (hs : s ∈ Rm) :
    idx16 (r * s) = xor16 (idx16 r) (idx16 s) := by
  have h1 : r * s ∈ Rm := Rm.mul_mem hr hs
  have e : el16 (idx16 (r * s)) = el16 (xor16 (idx16 r) (idx16 s)) := by
    rw [el16_idx16 h1, el16_xor, el16_idx16 hr, el16_idx16 hs]
  have := congrArg idx16 e
  rwa [idx16_el16, idx16_el16] at this

theorem yy5_mem_check : T5b yy5 = true :=
  Certificates.certificate5051.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem yy5_mem : yy5 ∈ T5 := mem_T5_of_b yy5_mem_check

theorem yy5_not_mem_check : yy5 ∈ Rml → False :=
  Certificates.certificate5051.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem yy5_not_mem : yy5 ∉ Rm := by
  intro h
  have : yy5 ∈ Rml := mem_Rm.1 h
  revert this
  exact yy5_not_mem_check

theorem yy5_sq : yy5 * yy5 = 1 :=
  Certificates.certificate5051.2.2.2.2.1

theorem T5_cases_chk :
    allT5.all (fun t => decide (t ∈ Rml ∨ t * yy5 ∈ Rml)) = true :=
  Certificates.certificate5051.2.2.2.2.2.1

theorem T5_cases
    {t : Amb 5} (ht : t ∈ T5) : t ∈ Rm ∨ t * yy5 ∈ Rm := by
  have h := T5_cases_chk
  simp only [List.all_eq_true, decide_eq_true_eq] at h
  rcases h t (mem_allT5.2 ht) with h1 | h1
  · exact Or.inl (mem_Rm.2 h1)
  · exact Or.inr (mem_Rm.2 h1)

theorem actF_yy5_chk :
    (List.finRange 16).all (fun i => decide (actF yy5 i = yHat i)) = true :=
  Certificates.certificate5051.2.2.2.2.2.2.1

theorem actF_yy5 (i : Fin 16) : actF yy5 i = yHat i := by
  have h := actF_yy5_chk
  simp only [List.all_eq_true, List.mem_finRange, decide_eq_true_eq] at h
  exact h i trivial

theorem actF_wm_chk :
    (List.finRange 16).all (fun i => decide (actF wm i = wHat i)) = true :=
  Certificates.certificate5051.2.2.2.2.2.2.2.1

theorem actF_wm (i : Fin 16) : actF wm i = wHat i := by
  have h := actF_wm_chk
  simp only [List.all_eq_true, List.mem_finRange, decide_eq_true_eq] at h
  exact h i trivial

theorem Sh0L_nodup : Sh0L.Nodup :=
  Certificates.certificate5051.2.2.2.2.2.2.2.2.1

theorem Sh0L_length : Sh0L.length = 128 :=
  Certificates.certificate5051.2.2.2.2.2.2.2.2.2.1

theorem Sh1L_nodup : Sh1L.Nodup :=
  Certificates.certificate5051.2.2.2.2.2.2.2.2.2.2.1

theorem Sh1L_length : Sh1L.length = 128 :=
  Certificates.certificate5051.2.2.2.2.2.2.2.2.2.2.2.1

theorem Sh0L_mul_chk : mulClosedChkP Sh0L = true :=
  Certificates.certificate5051.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem Sh0L_inv_chk : invClosedChkP Sh0L = true :=
  Certificates.certificate5051.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem Sh1L_mul_chk : mulClosedChkP Sh1L = true :=
  Certificates.certificate5051.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem Sh1L_inv_chk : invClosedChkP Sh1L = true :=
  Certificates.certificate5051.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem one_mem_Sh0L : (1 : Perm (Fin 16)) ∈ Sh0L :=
  Certificates.certificate5051.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

@[expose] def Sh0 : Subgroup (Perm (Fin 16)) :=
  lsub Sh0L one_mem_Sh0L
    (by simpa only [mulClosedChkP, List.all_eq_true, decide_eq_true_eq] using Sh0L_mul_chk)
    (by simpa only [invClosedChkP, List.all_eq_true, decide_eq_true_eq] using Sh0L_inv_chk)

@[expose] def Sh1 : Subgroup (Perm (Fin 16)) :=
  lsub Sh1L one_mem_Sh1L
    (by simpa only [mulClosedChkP, List.all_eq_true, decide_eq_true_eq] using Sh1L_mul_chk)
    (by simpa only [invClosedChkP, List.all_eq_true, decide_eq_true_eq] using Sh1L_inv_chk)

theorem mem_Sh0 {p : Perm (Fin 16)} : p ∈ Sh0 ↔ p ∈ Sh0L := Iff.rfl

theorem mem_Sh1 {p : Perm (Fin 16)} : p ∈ Sh1 ↔ p ∈ Sh1L := Iff.rfl

theorem card_Sh0 : Nat.card Sh0 = 128 := by
  rw [natCard_eq_length Sh0 Sh0L Sh0L_nodup (fun p => Iff.rfl)]
  exact Sh0L_length

theorem card_Sh1 : Nat.card Sh1 = 128 := by
  rw [natCard_eq_length Sh1 Sh1L Sh1L_nodup (fun p => Iff.rfl)]
  exact Sh1L_length

theorem emb48_mul0_chk : allT5.all (fun s => allT5.all fun t =>
    decide (emb48 tr16 yHat (s * t) = emb48 tr16 yHat s * emb48 tr16 yHat t)) = true :=
  Certificates.certificate5051.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem emb48_mul1_chk : allT5.all (fun s => allT5.all fun t =>
    decide (emb48 tr1 yHat1 (s * t) = emb48 tr1 yHat1 s * emb48 tr1 yHat1 t)) = true :=
  Certificates.certificate5051.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem emb48_inj0_chk : allT5.all (fun s => allT5.all fun t =>
    imp (decide (emb48 tr16 yHat s = emb48 tr16 yHat t)) (decide (s = t))) = true :=
  Certificates.certificate5051.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem emb48_inj1_chk : allT5.all (fun s => allT5.all fun t =>
    imp (decide (emb48 tr1 yHat1 s = emb48 tr1 yHat1 t)) (decide (s = t))) = true :=
  Certificates.certificate5051.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem emb48_mem0_chk :
    allT5.all (fun t => decide (emb48 tr16 yHat t ∈ Sh0L)) = true :=
  Certificates.certificate5051.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem emb48_mem1_chk :
    allT5.all (fun t => decide (emb48 tr1 yHat1 t ∈ Sh1L)) = true :=
  Certificates.certificate5051.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem S0L0_length : S0L0.length = 64 :=
  Certificates.certificate5051.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem S0L1_length : S0L1.length = 64 :=
  Certificates.certificate5051.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem R1L_sub_S0L0 :
    R1L.all (fun s => decide (s ∈ S0L0)) = true :=
  Certificates.certificate5051.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem R1L_length : R1L.length = 16 :=
  Certificates.certificate5051.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem RhatL0_sub :
    RhatL0.all (fun s => decide (s ∈ S0L0)) = true :=
  Certificates.certificate5051.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem RhatL1_sub :
    RhatL1.all (fun s => decide (s ∈ S0L1)) = true :=
  Certificates.certificate5051.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

@[expose] def elT
    (i : Fin 16) : ↥T5 := ⟨el16 i, Rm_le_T5 (el16_mem i)⟩

theorem f1_mem_T5_check : T5b f1 = true :=
  Certificates.certificate5051.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

theorem f1_mem_T5 : f1 ∈ T5 := mem_T5_of_b f1_mem_T5_check

@[expose] def x0T5 : ↥T5 := ⟨f1, f1_mem_T5⟩

theorem emb48_one0 : emb48 tr16 yHat 1 = 1 :=
  Certificates.certificate5051.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem emb48_one1 : emb48 tr1 yHat1 1 = 1 :=
  Certificates.certificate5051.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem emb48_mem0
    {t : Amb 5} (ht : t ∈ T5) : emb48 tr16 yHat t ∈ Sh0 := by
  have h := emb48_mem0_chk
  simp only [List.all_eq_true, decide_eq_true_eq] at h
  exact h t (mem_allT5.2 ht)

theorem emb48_mem1
    {t : Amb 5} (ht : t ∈ T5) : emb48 tr1 yHat1 t ∈ Sh1 := by
  have h := emb48_mem1_chk
  simp only [List.all_eq_true, decide_eq_true_eq] at h
  exact h t (mem_allT5.2 ht)

theorem emb48_mul0 {s t : Amb 5} (hs : s ∈ T5) (ht : t ∈ T5) :
    emb48 tr16 yHat (s * t) = emb48 tr16 yHat s * emb48 tr16 yHat t := by
  have h := emb48_mul0_chk
  simp only [List.all_eq_true, decide_eq_true_eq] at h
  exact h s (mem_allT5.2 hs) t (mem_allT5.2 ht)

theorem emb48_mul1 {s t : Amb 5} (hs : s ∈ T5) (ht : t ∈ T5) :
    emb48 tr1 yHat1 (s * t) = emb48 tr1 yHat1 s * emb48 tr1 yHat1 t := by
  have h := emb48_mul1_chk
  simp only [List.all_eq_true, decide_eq_true_eq] at h
  exact h s (mem_allT5.2 hs) t (mem_allT5.2 ht)

theorem emb48_inj0 {s t : Amb 5} (hs : s ∈ T5) (ht : t ∈ T5)
    (h : emb48 tr16 yHat s = emb48 tr16 yHat t) : s = t := by
  have h1 := emb48_inj0_chk
  simp only [List.all_eq_true, imp_eq_true, decide_eq_true_eq] at h1
  exact h1 s (mem_allT5.2 hs) t (mem_allT5.2 ht) h

theorem emb48_inj1 {s t : Amb 5} (hs : s ∈ T5) (ht : t ∈ T5)
    (h : emb48 tr1 yHat1 s = emb48 tr1 yHat1 t) : s = t := by
  have h1 := emb48_inj1_chk
  simp only [List.all_eq_true, imp_eq_true, decide_eq_true_eq] at h1
  exact h1 s (mem_allT5.2 hs) t (mem_allT5.2 ht) h

@[expose] def embHom0 : ↥T5 →* ↥Sh0 where
  toFun t := ⟨emb48 tr16 yHat t, emb48_mem0 t.2⟩
  map_one' := Subtype.ext emb48_one0
  map_mul' s t := Subtype.ext (emb48_mul0 s.2 t.2)

@[expose] def embHom1 : ↥T5 →* ↥Sh1 where
  toFun t := ⟨emb48 tr1 yHat1 t, emb48_mem1 t.2⟩
  map_one' := Subtype.ext emb48_one1
  map_mul' s t := Subtype.ext (emb48_mul1 s.2 t.2)

theorem embHom0_injective :
    Function.Injective embHom0 := fun s t h =>
  Subtype.ext (emb48_inj0 s.2 t.2 (congrArg Subtype.val h))

theorem embHom1_injective :
    Function.Injective embHom1 := fun s t h =>
  Subtype.ext (emb48_inj1 s.2 t.2 (congrArg Subtype.val h))

theorem one_mem_RhatL0 :
    (1 : Perm (Fin 16)) ∈ RhatL0 :=
  Certificates.certificate5051.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem one_mem_RhatL1 :
    (1 : Perm (Fin 16)) ∈ RhatL1 :=
  Certificates.certificate5051.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem one_mem_R1L : (1 : Perm (Fin 16)) ∈ R1L :=
  Certificates.certificate5051.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem one_mem_S0L0 : (1 : Perm (Fin 16)) ∈ S0L0 :=
  Certificates.certificate5051.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem one_mem_S0L1 : (1 : Perm (Fin 16)) ∈ S0L1 :=
  Certificates.certificate5051.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem RhatL0_mul_chk :
    mulClosedChkP RhatL0 = true :=
  Certificates.certificate5051.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem RhatL0_inv_chk :
    invClosedChkP RhatL0 = true :=
  Certificates.certificate5051.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem RhatL1_mul_chk :
    mulClosedChkP RhatL1 = true :=
  Certificates.certificate5051.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem RhatL1_inv_chk :
    invClosedChkP RhatL1 = true :=
  Certificates.certificate5051.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem R1L_mul_chk : mulClosedChkP R1L = true :=
  Certificates.certificate5051.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem R1L_inv_chk : invClosedChkP R1L = true :=
  Certificates.certificate5051.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem S0L0_mul_chk : mulClosedChkP S0L0 = true :=
  Certificates.certificate5051.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem S0L0_inv_chk : invClosedChkP S0L0 = true :=
  Certificates.certificate5051.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem S0L1_mul_chk : mulClosedChkP S0L1 = true :=
  Certificates.certificate5051.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem S0L1_inv_chk : invClosedChkP S0L1 = true :=
  Certificates.certificate5051.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

@[expose] def RsubP0 : Subgroup (Perm (Fin 16)) :=
  lsubP RhatL0 one_mem_RhatL0 RhatL0_mul_chk RhatL0_inv_chk

@[expose] def RsubP1 : Subgroup (Perm (Fin 16)) :=
  lsubP RhatL1 one_mem_RhatL1 RhatL1_mul_chk RhatL1_inv_chk

@[expose] def R1subP :
    Subgroup (Perm (Fin 16)) := lsubP R1L one_mem_R1L R1L_mul_chk R1L_inv_chk

@[expose] def S0subP0 :
    Subgroup (Perm (Fin 16)) := lsubP S0L0 one_mem_S0L0 S0L0_mul_chk S0L0_inv_chk

@[expose] def S0subP1 :
    Subgroup (Perm (Fin 16)) := lsubP S0L1 one_mem_S0L1 S0L1_mul_chk S0L1_inv_chk

theorem mem_RsubP0
    {p : Perm (Fin 16)} : p ∈ RsubP0 ↔ p ∈ RhatL0 := Iff.rfl
theorem mem_RsubP1
    {p : Perm (Fin 16)} : p ∈ RsubP1 ↔ p ∈ RhatL1 := Iff.rfl
theorem mem_R1subP
    {p : Perm (Fin 16)} : p ∈ R1subP ↔ p ∈ R1L := Iff.rfl
theorem mem_S0subP0
    {p : Perm (Fin 16)} : p ∈ S0subP0 ↔ p ∈ S0L0 := Iff.rfl
theorem mem_S0subP1
    {p : Perm (Fin 16)} : p ∈ S0subP1 ↔ p ∈ S0L1 := Iff.rfl

theorem RsubP0_le_Sh0_chk :
    RhatL0.all (fun p => decide (p ∈ Sh0L)) = true :=
  Certificates.certificate5051.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem RsubP1_le_Sh1_chk :
    RhatL1.all (fun p => decide (p ∈ Sh1L)) = true :=
  Certificates.certificate5051.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem S0subP0_le_Sh0_chk :
    S0L0.all (fun p => decide (p ∈ Sh0L)) = true :=
  Certificates.certificate5051.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem S0subP1_le_Sh1_chk :
    S0L1.all (fun p => decide (p ∈ Sh1L)) = true :=
  Certificates.certificate5051.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem R1subP_le_Sh0_chk :
    R1L.all (fun p => decide (p ∈ Sh0L)) = true :=
  Certificates.certificate5051.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

end CFSG.GH74.GLS.C3.Layer2.L5
