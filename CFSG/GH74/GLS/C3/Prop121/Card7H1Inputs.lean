module

public import CFSG.GH74.GLS.C3.Prop121.Card7Facts
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Card
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.GroupTheory.Perm.Fin
public meta import Mathlib.Algebra.Group.End
public meta import Mathlib.GroupTheory.Perm.Sign
public meta import Mathlib.GroupTheory.Perm.Basic
public meta import Mathlib.GroupTheory.Perm.Fin
public meta import Mathlib.Logic.Equiv.Fin.Basic
public meta import Mathlib.Logic.Equiv.Option
public meta import Mathlib.Data.List.FinRange
public import CFSG.GH74.GLS.C3.Layer3.Basic
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.InvolutionCountingOrderFormula
public import Mathlib.Algebra.BigOperators.Field

public section

namespace CFSG.GH74.GLS.C3.Prop121.Card7.HC

open Subgroup Equiv Perm CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model CFSG.GH74.GLS.Layer3
abbrev P11 : Type := Perm (Fin 11)

@[expose] def Y11 : P11 := swap 0 1 * swap 2 3 * (swap 4 5 * swap 6 7)

@[expose] def Hp (σ : P11) : Prop := sign σ = 1 ∧ σ * Y11 = Y11 * σ

instance : DecidablePred Hp :=
  fun σ => inferInstanceAs (Decidable (sign σ = 1 ∧ σ * Y11 = Y11 * σ))

@[expose] def flipsL : List P11 :=
  [(1 : P11), swap 0 1].flatMap fun a => [(1 : P11), swap 2 3].flatMap fun b =>
    [(1 : P11), swap 4 5].flatMap fun c => [(1 : P11), swap 6 7].map fun d => a * b * c * d

@[expose] def PS (i j : Fin 11) : P11 := swap i j * swap (i + 1) (j + 1)

@[expose] def s4L : List P11 :=
  [(0 : Fin 11), 2, 4, 6].flatMap fun a => [(0 : Fin 11), 2, 4].flatMap fun b =>
    [(0 : Fin 11), 2].map fun c => PS 6 a * PS 4 b * PS 2 c

@[expose] def s3L : List P11 :=
  [(8 : Fin 11), 9, 10].flatMap fun a => [(8 : Fin 11), 9].map fun b => swap 10 a * swap 9 b

@[expose] def H0 : List P11 :=
  flipsL.flatMap fun f => s4L.flatMap fun s => s3L.map fun t => f * s * t

@[expose] def HL : List P11 := H0.filter fun σ => decide (sign σ = 1)

end CFSG.GH74.GLS.C3.Prop121.Card7.HC
