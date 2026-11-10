
module

public import CFSG.GH74.GLS.C3.Layer2.L5Fin
public meta import Mathlib.GroupTheory.SpecificGroups.Alternating
public meta import CFSG.GH74.GLS.C3.Prop121.ModelFive
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelDefs
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelEmb
public meta import CFSG.GH74.GLS.C3.Layer2.NumMoved
public meta import CFSG.GH74.GLS.C3.Layer2.L5Fin
public import CFSG.GH74.GLS.C3.Layer2.L5A1Inputs
public meta import CFSG.GH74.GLS.C3.Layer2.L5A1Inputs

@[expose] public section

namespace CFSG.GH74.GLS.C3.Layer2.L5

open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2
  CFSG.GH74.GLS.C3.Layer2.Model

def lsub {M : Type*} [Group M] (l : List M) (h1 : (1 : M) ∈ l)
    (hm : ∀ a ∈ l, ∀ b ∈ l, a * b ∈ l) (hi : ∀ a ∈ l, a⁻¹ ∈ l) : Subgroup M where
  carrier := {p | p ∈ l}
  one_mem' := h1
  mul_mem' := fun {a b} ha hb => hm a ha b hb
  inv_mem' := fun {a} ha => hi a ha

theorem mem_lsub {M : Type*} [Group M] {l : List M} {h1 : (1 : M) ∈ l}
    {hm : ∀ a ∈ l, ∀ b ∈ l, a * b ∈ l} {hi : ∀ a ∈ l, a⁻¹ ∈ l} {p : M} :
    p ∈ lsub l h1 hm hi ↔ p ∈ l := Iff.rfl

theorem mul_of_chk {l : List (Amb 5)} (h : mulClosedChk l = true) :
    ∀ a ∈ l, ∀ b ∈ l, a * b ∈ l := by
  simpa only [mulClosedChk, List.all_eq_true, decide_eq_true_eq] using h

theorem inv_of_chk {l : List (Amb 5)} (h : invClosedChk l = true) : ∀ a ∈ l, a⁻¹ ∈ l := by
  simpa only [invClosedChk, List.all_eq_true, decide_eq_true_eq] using h

theorem one_mem_Pml : (1 : Amb 5) ∈ Pml := by simp [Pml]

theorem one_mem_Qml : (1 : Amb 5) ∈ Qml := by simp [Qml]

theorem mem_Km {p : Amb 5} : p ∈ Km ↔ p.2 = 1 ∧ sign p.1 = 1 := by
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    exact ⟨rfl, mem_alternatingGroup.1 hσ⟩
  · rintro ⟨h2, h1⟩
    exact ⟨p.1, mem_alternatingGroup.2 h1, Prod.ext rfl h2.symm⟩

theorem Km_le_Fgrp : Km ≤ Fgrp 5 := fun p hp => by
  obtain ⟨h2, h1⟩ := mem_Km.1 hp
  rw [mem_Fgrp5, h2]
  simp [h1]

theorem card_Km : Nat.card Km = 60 := by
  rw [Km, Subgroup.card_map_of_injective (fun σ τ h => by simpa using congrArg Prod.fst h),
    nat_card_alternatingGroup]
  simp [Nat.factorial]

theorem f1_snd : f1.2 = x4 := rfl

theorem f2_snd : f2.2 = y4 := rfl

end CFSG.GH74.GLS.C3.Layer2.L5
