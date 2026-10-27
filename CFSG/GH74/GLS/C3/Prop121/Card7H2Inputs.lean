module

public import CFSG.GH74.GLS.C3.Prop121.Card7H1
public meta import CFSG.GH74.GLS.C3.Prop121.Card7H1
public meta import Mathlib.Algebra.Group.End
public meta import Mathlib.GroupTheory.Perm.Sign
public meta import Mathlib.GroupTheory.Perm.Basic
public meta import Mathlib.GroupTheory.Perm.Fin
public meta import Mathlib.Logic.Equiv.Fin.Basic
public meta import Mathlib.Logic.Equiv.Option
public meta import Mathlib.Data.List.FinRange

public section

namespace CFSG.GH74.GLS.C3.Prop121.Card7.HC

open Subgroup Equiv Perm CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model CFSG.GH74.GLS.Layer3
@[expose] def ord3Check : Bool :=
  HL.all fun σ => decide (σ ^ 3 = 1 → σ ≠ 1 →
    (((σ = T1 ∨ σ = T1⁻¹) ∧ ccL σ σ = 576) ∨ ccL σ σ ≤ 36))

@[expose] def centerCheck : Bool :=
  HL.all fun σ => decide ((HL.all fun h => decide (h * σ = σ * h)) = true → σ = 1 ∨ σ = Y11)

@[expose] def B0invCheck : Bool :=
  HL.all fun b => decide (b * T1 = T1 * b → b * b = 1 → b ≠ 1 → b ≠ Y11 →
    ccL T1 b = 48 ∨ ccL T1 b = 96)

end CFSG.GH74.GLS.C3.Prop121.Card7.HC
