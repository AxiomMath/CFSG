module

public import CFSG.GH74.GLS.C3.Prop121.Card7F1
public import CFSG.GH74.GLS.C3.Layer2.FinModelEnum
public import CFSG.GH74.GLS.C3.Layer2.FinModelCard
public import Mathlib.GroupTheory.Sylow
public meta import CFSG.GH74.GLS.C3.Prop121.Card7F1
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelEnum
public meta import Mathlib.Data.List.Dedup
public import CFSG.GH74.GLS.C3.Prop121.Card7F5Inputs
public meta import CFSG.GH74.GLS.C3.Prop121.Card7F5Inputs
public import Certificates.Certificate5039
public import Certificates.Certificate5079

public section

namespace CFSG.GH74.GLS.C3.Prop121.Card7.FF

open Subgroup Equiv Perm CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model

theorem card_F7 : Nat.card F7 = 20160 := by
  rw [card_Fgrp_eq 7]
  decide

theorem factorization_card_F7 : (Nat.card F7).factorization 2 = 6 := by
  rw [card_F7, Nat.factorization_def _ Nat.prime_two]
  decide +kernel

theorem exists_sylow_conj (P : Subgroup F7) (hP : Nat.card P = 64) (S0 : Sylow 2 F7) :
    ∃ g : F7, ∀ x : F7, x ∈ P ↔ g⁻¹ * x * g ∈ (S0 : Subgroup F7) := by
  have hP' : Nat.card P = 2 ^ (Nat.card F7).factorization 2 := by
    rw [factorization_card_F7, hP]
    norm_num
  let SP : Sylow 2 F7 := Sylow.ofCard P hP'
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq F7 S0 SP
  refine ⟨g, fun x => ?_⟩
  have h1 : ((g • S0 : Sylow 2 F7) : Subgroup F7) = P := by
    rw [hg]
    rfl
  rw [← h1, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨s, hs, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hs
  · intro hx
    refine ⟨g⁻¹ * x * g, hx, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]

theorem exists_sylow_T0 :
    ∃ S0 : Sylow 2 F7, ∀ x : F7, x ∈ (S0 : Subgroup F7) ↔ (x : Amb 7) ∈ Tl 7 := by
  obtain ⟨S0, hS0⟩ := isSylow_T0_aux 7 (Or.inr rfl)
  refine ⟨S0, fun x => ?_⟩
  rw [← mem_T0_iff 7 (Or.inr rfl), ← hS0]
  simp [Subgroup.mem_map]

theorem mem_XAll {s : F7} : s ∈ XAll ↔ XF s := by simp [XAll, mem_F7L]

theorem XAll_nodup : XAll.Nodup := F7L_nodup.filter _

theorem chk_syl :
    XAll.countP (fun s : F7 => decide ((s : Amb 7) ∈ Tl 7)) = 14 :=
  Certificates.certificate5079

theorem F7_sylow_count :
    ∀ P : Subgroup F7, Nat.card P = 64 → Nat.card {f : P // XF (f : F7)} = 14 := by
  intro P hP
  obtain ⟨S0, hS0⟩ := exists_sylow_T0
  obtain ⟨g, hg⟩ := exists_sylow_conj P hP S0
  have e1 : Nat.card {f : P // XF (f : F7)} = Nat.card {x : F7 // XF x ∧ (x : Amb 7) ∈ Tl 7} := by
    refine Nat.card_congr ?_
    refine (Equiv.subtypeSubtypeEquivSubtypeInter (fun x : F7 => x ∈ P) XF).trans ?_
    refine Equiv.subtypeEquiv (MulAut.conj g⁻¹).toEquiv (fun x => ?_)
    have h1 : (MulAut.conj g⁻¹).toEquiv x = g⁻¹ * x * g := by simp
    rw [h1, hg x, hS0 (g⁻¹ * x * g)]
    have h2 := xf_conj_iff g⁻¹ x
    rw [inv_inv] at h2
    rw [h2]
    exact and_comm
  have h := card_subtype_eq_countP XAll XAll_nodup (fun x : F7 => XF x ∧ (x : Amb 7) ∈ Tl 7)
    (fun s : F7 => decide ((s : Amb 7) ∈ Tl 7)) (fun x => by rw [mem_XAll, decide_eq_true_eq])
  rw [e1, h]
  exact chk_syl

end CFSG.GH74.GLS.C3.Prop121.Card7.FF
