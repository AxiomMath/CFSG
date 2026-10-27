module

public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.Data.List.FinRange
public meta import Mathlib.Algebra.Group.End
public meta import Mathlib.GroupTheory.Perm.Sign
public meta import Mathlib.GroupTheory.Perm.Basic
public meta import Mathlib.GroupTheory.Perm.Fin
public meta import Mathlib.Logic.Equiv.Fin.Basic
public meta import Mathlib.Logic.Equiv.Option
public meta import Mathlib.Data.List.FinRange

public section

namespace CFSG.GH74.GLS.C3.Prop121

open Equiv Perm
@[expose] def allPerms : (m : ℕ) → List (Perm (Fin m))
  | 0 => [1]
  | m + 1 => (List.finRange (m + 1)).flatMap fun p =>
      (allPerms m).map fun e => Equiv.Perm.decomposeFin.symm (p, e)

@[expose] def cEnd7 : Perm (Fin 8) := swap 5 6 * swap 6 7

@[expose] def evenL7 : List (Perm (Fin 8)) :=
  (allPerms 8).filter fun s => s * s = 1 ∧ sign s = 1 ∧ s * cEnd7 * s⁻¹ = cEnd7⁻¹

@[expose] def a4L7 : List (Perm (Fin 8)) :=
  (allPerms 8).filter fun s => s * s = 1 ∧ sign s = 1 ∧ s ≠ 1 ∧ (cEnd7 * s) ^ 3 = 1

@[expose] def oddL7 : List (Perm (Fin 8)) :=
  (allPerms 8).filter fun s => s * s = 1 ∧ sign s = -1 ∧ s * cEnd7 * s⁻¹ = cEnd7⁻¹

@[expose] def okC7 (E2 : List (Perm (Fin 8))) (s1 s2 s3 s4 : Perm (Fin 8)) : Bool :=
  E2.all fun s5 =>
    if (s4 * s5) ^ 3 = 1 then if (s2 * s5) ^ 2 = 1 then if (s3 * s5) ^ 2 = 1 then
      decide ((s1 * s2) ^ 3 = 1) else true else true else true

@[expose] def okB7 (E1 E2 : List (Perm (Fin 8))) (s1 : Perm (Fin 8)) : Bool :=
  E1.all fun s2 => E2.all fun s3 =>
    if (s2 * s3) ^ 3 = 1 then if s2 ≠ s3 then E2.all fun s4 =>
      if (s3 * s4) ^ 3 = 1 then if (s2 * s4) ^ 2 = 1 then if s2 ≠ s4 then okC7 E2 s1 s2 s3 s4
        else true else true else true else true else true

@[expose] def okAll7 (A O E : List (Perm (Fin 8))) : Bool :=
  A.all fun s1 => O.all fun sg => if sg * s1 = s1 * sg then
    okB7 (E.filter fun s => sg * s = s * sg)
      ((E.filter fun s => sg * s = s * sg).filter fun s => s * s1 = s1 * s) s1 else true

end CFSG.GH74.GLS.C3.Prop121
