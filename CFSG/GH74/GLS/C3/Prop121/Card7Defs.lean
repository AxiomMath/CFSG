module

public import CFSG.GH74.GLS.C3.Layer2.FinModelDefs
public import CFSG.GH74.GLS.C3.Layer2.NumMoved
public import CFSG.GH74.GLS.C3.Layer3.AltInvolutions
public import Mathlib.Data.Rat.Floor

public section

namespace CFSG.GH74.GLS.C3.Prop121.Card7

open Subgroup Equiv Perm CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model CFSG.GH74.GLS.Layer3

abbrev F7 : Type := ↥(Fgrp 7)

abbrev A11 : Type := ↥(alternatingGroup (Fin 11))

@[expose] def altY11 : A11 := altY (by norm_num : 8 ≤ 11)

abbrev H11 : Type := ↥(centralizer ({altY11} : Set A11))

@[expose] def nm7 (a : Amb 7) : ℕ := numMoved a.1 + numMoved a.2

@[expose] def IsInv {M : Type*} [Group M] (a : M) : Prop := a ^ 2 = 1 ∧ a ≠ 1

theorem isInv_iff_orderOf {M : Type*} [Group M] {a : M} : IsInv a ↔ orderOf a = 2 := by
  unfold IsInv
  constructor
  · rintro ⟨h1, h2⟩
    exact orderOf_eq_prime h1 h2
  · intro h
    refine ⟨?_, ?_⟩
    · rw [← h]; exact pow_orderOf_eq_one a
    · intro h1
      rw [h1, orderOf_one] at h
      omega

@[expose] def XF (f : F7) : Prop := IsInv f ∧ nm7 (f : Amb 7) = 4

@[expose] def YF (f : F7) : Prop := IsInv f ∧ nm7 (f : Amb 7) = 8

@[expose] def Ty3 (f : F7) : Prop :=
  (f : Amb 7).2 = 1 ∧ f ^ 3 = 1 ∧ numMoved (f : Amb 7).1 = 3

@[expose] def Ty33 (f : F7) : Prop :=
  (f : Amb 7).2 = 1 ∧ f ^ 3 = 1 ∧ numMoved (f : Amb 7).1 = 6

@[expose] def f0 : F7 :=
  ⟨(swap 0 1 * swap 1 2, 1), by
    refine ⟨by simp, ?_⟩
    show sign (swap (0 : Fin 7) 1 * swap 1 2) = sign (1 : Perm (Fin 4))
    simp [Perm.sign_mul]⟩

theorem f0_pow_three : f0 ^ 3 = 1 := by
  apply Subtype.ext
  simp only [Subgroup.coe_pow, Subgroup.coe_one]
  refine Prod.ext ?_ (by simp [f0])
  show (swap (0 : Fin 7) 1 * swap 1 2) ^ 3 = 1
  decide

theorem f0_ne_one : f0 ≠ 1 := by
  intro h
  have h1 := congrArg (fun f : F7 => ((f : Amb 7).1) (0 : Fin 7)) h
  revert h1
  simp only [f0, Subgroup.coe_one]
  decide

@[expose] def x0F : F7 := ⟨x0 7, x0_mem_Fgrp 7⟩

@[expose] noncomputable def ccard (M : Type*) [Group M] (u v : M) : ℕ :=
  Nat.card {c : M // c * u = u * c ∧ c * v = v * c}

end CFSG.GH74.GLS.C3.Prop121.Card7
