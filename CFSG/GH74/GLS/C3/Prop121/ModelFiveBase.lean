
module

public import CFSG.GH74.GLS.C3.Layer2.FinModelEmb
public import CFSG.GH74.GLS.C3.Layer2.NumMoved
public import CFSG.GH74.GLS.C3.Layer2.FinModelCard
public import Mathlib.Data.List.FinRange
public import Mathlib.GroupTheory.Perm.Fin
public meta import Mathlib.GroupTheory.SpecificGroups.Alternating
public meta import Mathlib.GroupTheory.Perm.Fin
public meta import Mathlib.Logic.Equiv.Fin.Basic
public meta import Mathlib.Logic.Equiv.Option
public meta import Mathlib.Data.List.FinRange
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelDefs
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelEmb
public meta import CFSG.GH74.GLS.C3.Layer2.NumMoved
public import CFSG.GH74.GLS.C3.Prop121.ModelFiveInputs
public meta import CFSG.GH74.GLS.C3.Prop121.ModelFiveInputs

@[expose] public section

namespace CFSG.GH74.GLS.C3.Prop121

open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model

@[expose] def T5 : Subgroup (Amb 5) :=
  Fgrp 5 ⊓ (Subgroup.centralizer ({z5} : Set (Perm (Fin 5)))).prod ⊤

theorem mem_T5 {p : Amb 5} :
    p ∈ T5 ↔ p.2 * x4 = x4 * p.2 ∧ sign p.1 = sign p.2 ∧ p.1 * z5 = z5 * p.1 := by
  simp only [T5, Subgroup.mem_inf, Subgroup.mem_prod, Subgroup.mem_top, and_true,
    Subgroup.mem_centralizer_singleton_iff]
  exact and_assoc

theorem T5_le_Fgrp : T5 ≤ Fgrp 5 := inf_le_left

theorem mem_T5_iff_b {p : Amb 5} : p ∈ T5 ↔ T5b p = true := by
  rw [mem_T5, T5b, decide_eq_true_iff]

theorem mem_g5Perms : ∀ (m : ℕ) (s : Perm (Fin m)), s ∈ g5Perms m
  | 0, s => by simp [g5Perms, Subsingleton.elim s 1]
  | m + 1, s => by
      unfold g5Perms
      simp only [List.mem_flatMap, List.mem_finRange, true_and, List.mem_map]
      obtain ⟨p, e⟩ := Equiv.Perm.decomposeFin s
      refine ⟨(Equiv.Perm.decomposeFin s).1, (Equiv.Perm.decomposeFin s).2,
        mem_g5Perms m _, ?_⟩
      exact Equiv.Perm.decomposeFin.symm_apply_apply s

theorem mem_allAmb5 (p : Amb 5) : p ∈ allAmb5 := by
  simp only [allAmb5, List.mem_flatMap, List.mem_map]
  exact ⟨p.1, mem_g5Perms 5 _, p.2, mem_g5Perms 4 _, rfl⟩

theorem mem_allT5 {p : Amb 5} : p ∈ allT5 ↔ p ∈ T5 := by
  rw [allT5, List.mem_filter, mem_T5_iff_b]
  exact ⟨fun h => h.2, fun h => ⟨mem_allAmb5 p, h⟩⟩

theorem allT5_length : allT5.length = 32 := by
  decide +kernel

theorem allT5_nodup : allT5.Nodup := by
  decide +kernel

theorem allT5_facts : allT5.length = 32 ∧ allT5.Nodup :=
  ⟨allT5_length, allT5_nodup⟩

theorem natCard_eq_length {M : Type*} [Group M] [DecidableEq M] (H : Subgroup M) (L : List M)
    (hL : L.Nodup) (hmem : ∀ p, p ∈ H ↔ p ∈ L) : Nat.card H = L.length := by
  have : Nat.card H = Nat.card (L.toFinset) := by
    apply Nat.card_congr
    exact Equiv.subtypeEquivRight (fun g => by simpa using hmem g)
  rw [this, Nat.card_eq_fintype_card, Fintype.card_coe, List.toFinset_card_of_nodup hL]

theorem card_T5 : Nat.card T5 = 32 := by
  rw [natCard_eq_length T5 allT5 allT5_facts.2 (fun p => mem_allT5.symm), allT5_facts.1]

theorem mem_Fgrp5 {p : Amb 5} : p ∈ Fgrp 5 ↔ p.2 * x4 = x4 * p.2 ∧ sign p.1 = sign p.2 := Iff.rfl

instance (u₁ w : Amb 5) : Decidable (W1P u₁ w) := by unfold W1P; infer_instance

instance (w u : Amb 5) : Decidable (U1P w u) := by unfold U1P; infer_instance

structure IsAutOn (b : Amb 5 → Amb 5) : Prop where
  mem : ∀ p ∈ T5, b p ∈ T5
  mul : ∀ p ∈ T5, ∀ q ∈ T5, b (p * q) = b p * b q
  inj : ∀ p ∈ T5, ∀ q ∈ T5, b p = b q → p = q
  surj : ∀ q ∈ T5, ∃ p ∈ T5, b p = q

theorem mem_T5_of_b {p : Amb 5} (h : T5b p = true) : p ∈ T5 := mem_T5_iff_b.2 h

theorem IsAutOn.one {b : Amb 5 → Amb 5} (hb : IsAutOn b) : b 1 = 1 := by
  have h := hb.mul 1 (one_mem _) 1 (one_mem _)
  rw [mul_one] at h
  exact mul_left_cancel (a := b 1) (by rw [mul_one]; exact h.symm)

theorem T5_sign_of_snd {v : Amb 5} (hv : v ∈ T5) (h2 : v.2 = 1) : sign v.1 = 1 := by
  have := (mem_T5.1 hv).2.1
  rw [h2, map_one] at this
  exact this

end CFSG.GH74.GLS.C3.Prop121
