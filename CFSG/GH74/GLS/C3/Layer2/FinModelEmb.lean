module

public import CFSG.GH74.GLS.C3.Layer2.FinModelDefs
public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.GH74.GLS.C3.Layer2.Model

open Equiv Perm Subgroup

@[expose] def emb (n : ℕ) : Amb n →* Perm (Fin (n + 4)) :=
  (Equiv.permCongrHom finSumFinEquiv).toMonoidHom.comp (Equiv.Perm.sumCongrHom (Fin n) (Fin 4))

theorem sign_emb (n : ℕ) (p : Amb n) : sign (emb n p) = sign p.1 * sign p.2 := by
  simp [emb, Equiv.permCongrHom, sign_permCongr, sign_sumCongr]

theorem emb_injective (n : ℕ) : Function.Injective (emb n) := by
  intro p q h
  have h1 : (Equiv.permCongrHom finSumFinEquiv).toMonoidHom
      (Equiv.Perm.sumCongrHom (Fin n) (Fin 4) p) =
      (Equiv.permCongrHom finSumFinEquiv).toMonoidHom
      (Equiv.Perm.sumCongrHom (Fin n) (Fin 4) q) := h
  exact Equiv.Perm.sumCongrHom_injective ((Equiv.permCongrHom finSumFinEquiv).injective h1)

theorem emb_mem_alternating (n : ℕ) {p : Amb n} (hp : p ∈ Fgrp n) :
    emb n p ∈ alternatingGroup (Fin (n + 4)) := by
  rw [mem_alternatingGroup, sign_emb, hp.2]
  rcases Int.units_eq_one_or (sign p.2) with h | h <;> simp [h]

@[expose] def embA (n : ℕ) : Fgrp n →* alternatingGroup (Fin (n + 4)) :=
  ((emb n).comp (Fgrp n).subtype).codRestrict (alternatingGroup (Fin (n + 4)))
    (fun p => emb_mem_alternating n p.2)

theorem embA_injective (n : ℕ) : Function.Injective (embA n) := by
  intro p q h
  apply Subtype.ext
  apply emb_injective n
  exact congrArg Subtype.val h

@[expose] def embT (n : ℕ) [NeZero n] : T0 n →* alternatingGroup (Fin (n + 4)) :=
  (embA n).comp (Subgroup.inclusion (T0_le_Fgrp n))

theorem embT_injective (n : ℕ) [NeZero n] : Function.Injective (embT n) := by
  intro p q h
  apply Subtype.ext
  apply emb_injective n
  exact congrArg Subtype.val h

theorem embT_coe (n : ℕ) [NeZero n] (t : T0 n) :
    ((embT n t : alternatingGroup (Fin (n + 4))) : Perm (Fin (n + 4))) = emb n (t : Amb n) := rfl

@[expose] def a0perm (n : ℕ) [NeZero n] : Perm (Fin (n + 4)) :=
  swap (Fin.castAdd 4 (0 : Fin n)) (Fin.natAdd n 0) *
    swap (Fin.castAdd 4 (1 : Fin n)) (Fin.natAdd n 1) *
    swap (Fin.castAdd 4 (2 : Fin n)) (Fin.natAdd n 2) *
    swap (Fin.castAdd 4 (3 : Fin n)) (Fin.natAdd n 3)

end CFSG.GH74.GLS.C3.Layer2.Model
