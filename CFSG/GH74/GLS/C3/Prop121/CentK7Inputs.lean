module

public import CFSG.GH74.GLS.C3.Prop121.L122FinInputs
public import Mathlib.GroupTheory.Perm.Cycle.Type
public meta import Mathlib.Algebra.Group.End
public meta import Mathlib.GroupTheory.Perm.Sign
public meta import Mathlib.GroupTheory.Perm.Basic
public meta import Mathlib.GroupTheory.Perm.Fin
public meta import Mathlib.GroupTheory.Perm.Support
public meta import Mathlib.GroupTheory.Perm.Cycle.Basic
public meta import Mathlib.GroupTheory.Perm.Cycle.Type
public meta import Mathlib.Logic.Equiv.Fin.Basic
public meta import Mathlib.Logic.Equiv.Option
public meta import Mathlib.Data.List.FinRange

public section

namespace CFSG.GH74.GLS.C3.Prop121

open Subgroup Equiv Perm CFSG.GH74.GLS CFSG.GH74.GLS.C3.Layer2.Model
@[expose] def tauA7 : Perm (Fin 7) := swap 0 1 * swap 0 2

@[expose] def tauB7 : Perm (Fin 7) := tauA7 * (swap 3 4 * swap 3 5)

@[expose] def even7 : List (Perm (Fin 7)) :=
  (allPerms 7).filter fun s => sign s = 1

@[expose] def goodW7 (a1 a2 c : Perm (Fin 7)) : Bool :=
  decide (c * a1 = a1 * c ∧ c ≠ 1 ∧ c ≠ a1 ∧ c ≠ a2 ∧ c ≠ a1 * a2)

@[expose] def wordW7 (a1 a2 β : Perm (Fin 7)) : Bool :=
  goodW7 a1 a2 (β * a2 * β⁻¹ * a1 * a2 * β)

@[expose] def okBeta7 (a1 a2 τ b : Perm (Fin 7)) : Bool :=
  wordW7 a1 a2 b || wordW7 a1 a2 (b * τ) || wordW7 a1 a2 (b * τ⁻¹)

@[expose] def centE7 (τ : Perm (Fin 7)) : List (Perm (Fin 7)) :=
  even7.filter fun b => b * τ = τ * b ∧ b ≠ 1 ∧ b ≠ τ ∧ b ≠ τ⁻¹

@[expose] def okPair7 (C : List (Perm (Fin 7))) (τ a1 a2 : Perm (Fin 7)) : Bool :=
  if (τ * a1 * τ⁻¹ = a2 ∨ τ * a1 * τ⁻¹ = a1 * a2) ∧
      (τ * a2 * τ⁻¹ = a1 ∨ τ * a2 * τ⁻¹ = a2 ∨ τ * a2 * τ⁻¹ = a1 * a2) then
    C.all (okBeta7 a1 a2 τ)
  else true

@[expose] def okTauC7 (C : List (Perm (Fin 7))) (τ : Perm (Fin 7)) : Bool :=
  inv7.all fun a1 => inv7.all fun a2 =>
    if a1 * a2 = a2 * a1 ∧ a1 ≠ a2 then okPair7 C τ a1 a2 else true

@[expose] def okTau7 (τ : Perm (Fin 7)) : Bool := okTauC7 (centE7 τ) τ

@[expose] def okSearch7 : Bool := okTau7 tauA7 && okTau7 tauB7

end CFSG.GH74.GLS.C3.Prop121
