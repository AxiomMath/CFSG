module

public import CFSG.GH74.GLS.C3.Prop121.ModelFive
public import CFSG.GH74.GLS.C3.Layer2.FinModelFactsGeneric
public import Mathlib.GroupTheory.Sylow
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public meta import Mathlib.GroupTheory.SpecificGroups.Alternating
public meta import CFSG.GH74.GLS.C3.Prop121.ModelFive
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelDefs
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelEmb
public meta import CFSG.GH74.GLS.C3.Layer2.NumMoved
public import CFSG.GH74.GLS.C3.Layer2.FinModelFactsData

public section

namespace CFSG.GH74.GLS.C3.Prop121

open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model CFSG.GH74.GLS.C3.Layer2.Model.Facts
@[expose] def S0l : List (Perm (Fin 9)) :=
  allT5.flatMap fun t => [emb 5 t, emb 5 t * a0perm 5]

@[expose] def classPair (L : List (Perm (Fin 9))) (y y' : Perm (Fin 9)) : Bool :=
  !(decide (y ≠ y') && decide (y * y = 1) && decide (numMoved y = 4) &&
    L.all fun s => (decide (s * y * s⁻¹ = y) || decide (s * y * s⁻¹ = y')) &&
      (decide (s * y' * s⁻¹ = y) || decide (s * y' * s⁻¹ = y'))) ||
    decide (y = emb 5 f1) || decide (y = emb 5 e1)

@[expose] def classAll (L : List (Perm (Fin 9))) : Bool :=
  L.all fun y => L.all fun y' => classPair L y y'

@[expose] def centAll (L : List (Perm (Fin 9))) (T : List (Amb 5)) : Bool :=
  L.all fun p => !decide (p * emb 5 f1 = emb 5 f1 * p) || T.any fun t => decide (emb 5 t = p)

end CFSG.GH74.GLS.C3.Prop121
