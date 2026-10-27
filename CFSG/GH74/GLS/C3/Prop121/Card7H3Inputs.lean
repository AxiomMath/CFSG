module

public import CFSG.GH74.GLS.C3.Prop121.Card7H1
public import CFSG.GH74.GLS.C3.Prop121.Card7H2
public import Mathlib.Data.List.Sublists
public import Mathlib.Data.List.ProdSigma
public import Mathlib.Data.List.Nodup
public meta import CFSG.GH74.GLS.C3.Prop121.Card7H1
public meta import Batteries.Data.List.Basic
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
@[expose] def B0L : List P11 := HL.filter fun σ => decide (σ * T1 = T1 * σ)

@[expose] def IL : List P11 := B0L.filter fun σ => decide (σ * σ = 1 ∧ σ ≠ 1)

@[expose] def cl96 : List P11 := IL.filter fun σ => decide (ccL T1 σ = 96)

@[expose] def cl48 : List P11 := IL.filter fun σ => decide (ccL T1 σ = 48)

@[expose] def classesAux : ℕ → List P11 → List (P11 × List P11)
  | 0, _ => []
  | _ + 1, [] => []
  | n + 1, r :: rest =>
    (r, (r :: rest).filter fun b => B0L.any fun g => decide (g * r * g⁻¹ = b)) ::
      classesAux n ((r :: rest).filter fun b => !(B0L.any fun g => decide (g * r * g⁻¹ = b)))

@[expose] def classes : List (P11 × List P11) := classesAux 43 IL

@[expose] def ZR (R : List (P11 × List P11)) (b : P11) : Bool := R.any fun c => decide (b ∈ c.2)

@[expose] def yPow (g : P11) : Bool := (List.range 12).any fun k => decide (g ^ k = Y11)

@[expose] def pairCount (R : List (P11 × List P11)) : ℕ :=
  ((IL.filter (ZR R)) ×ˢ (IL.filter fun b => !ZR R b)).countP fun p => yPow (p.1 * p.2)

@[expose] def classesCheck : Bool :=
  (IL.all fun b => classes.any fun c => decide (b ∈ c.2)) &&
  (classes.all fun c => c.2.all fun b => B0L.any fun g => decide (g * c.1 * g⁻¹ = b)) &&
  decide (Y11 ∈ IL)

@[expose] def powCheck : Bool := IL.all fun a => IL.all fun b => decide ((a * b) ^ 12 = 1)

@[expose] def ryCheck : Bool :=
  classes.sublists.all fun R =>
    decide ((cl96.filter (ZR R)).length = 6 → (cl48.filter (ZR R)).length = 12 →
      ZR R Y11 = false → pairCount R = 156)

end CFSG.GH74.GLS.C3.Prop121.Card7.HC
