module

public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.Data.Fintype.Perm
public meta import Mathlib.Algebra.Group.End
public meta import Mathlib.GroupTheory.Perm.Sign
public meta import Mathlib.GroupTheory.Perm.Basic
public meta import Mathlib.Data.Fintype.Perm

public section

namespace CFSG.GH74.GLS.C3.Prop121

open Equiv Perm
@[expose] def cEnd5 : Perm (Fin 6) := swap 3 4 * swap 4 5

@[expose] def evenC5 : Finset (Perm (Fin 6)) :=
  Finset.univ.filter fun s => s * s = 1 ∧ sign s = 1 ∧ s * cEnd5 * s⁻¹ = cEnd5⁻¹

@[expose] def a4C5 : Finset (Perm (Fin 6)) :=
  Finset.univ.filter fun s => s * s = 1 ∧ sign s = 1 ∧ s ≠ 1 ∧ (cEnd5 * s) ^ 3 = 1

@[expose] def oddC5 : Finset (Perm (Fin 6)) :=
  Finset.univ.filter fun s => s * s = 1 ∧ sign s = -1 ∧ s * cEnd5 * s⁻¹ = cEnd5⁻¹

@[expose] def searchB5 (E1 E2 : Finset (Perm (Fin 6))) (s1 : Perm (Fin 6)) : Prop :=
  ∀ s2 ∈ E1, ∀ s3 ∈ E2, (s2 * s3) ^ 3 = 1 → s2 ≠ s3 → (s1 * s2) ^ 3 = 1

@[expose] def searchAll5 (A O E : Finset (Perm (Fin 6))) : Prop :=
  ∀ s1 ∈ A, ∀ sg ∈ O, sg * s1 = s1 * sg →
    searchB5 (E.filter fun s => sg * s = s * sg)
      ((E.filter fun s => sg * s = s * sg).filter fun s => s * s1 = s1 * s) s1

@[expose] def cEnd6 : Perm (Fin 7) := swap 4 5 * swap 5 6

@[expose] def evenC6 : Finset (Perm (Fin 7)) :=
  Finset.univ.filter fun s => s * s = 1 ∧ sign s = 1 ∧ s * cEnd6 * s⁻¹ = cEnd6⁻¹

@[expose] def a4C6 : Finset (Perm (Fin 7)) :=
  Finset.univ.filter fun s => s * s = 1 ∧ sign s = 1 ∧ s ≠ 1 ∧ (cEnd6 * s) ^ 3 = 1

@[expose] def oddC6 : Finset (Perm (Fin 7)) :=
  Finset.univ.filter fun s => s * s = 1 ∧ sign s = -1 ∧ s * cEnd6 * s⁻¹ = cEnd6⁻¹

@[expose] def searchB6 (E1 E2 : Finset (Perm (Fin 7))) (s1 : Perm (Fin 7)) : Prop :=
  ∀ s2 ∈ E1, ∀ s3 ∈ E2, (s2 * s3) ^ 3 = 1 → s2 ≠ s3 →
    ∀ s4 ∈ E2, (s3 * s4) ^ 3 = 1 → (s2 * s4) ^ 2 = 1 → s2 ≠ s4 → (s1 * s2) ^ 3 = 1

@[expose] def searchAll6 (A O E : Finset (Perm (Fin 7))) : Prop :=
  ∀ s1 ∈ A, ∀ sg ∈ O, sg * s1 = s1 * sg →
    searchB6 (E.filter fun s => sg * s = s * sg)
      ((E.filter fun s => sg * s = s * sg).filter fun s => s * s1 = s1 * s) s1

end CFSG.GH74.GLS.C3.Prop121
