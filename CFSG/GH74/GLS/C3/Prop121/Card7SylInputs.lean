module

public import CFSG.GH74.GLS.C3.Prop121.Card7Facts2
public import CFSG.GH74.GLS.C3.Prop121.Card7H1
public meta import CFSG.GH74.GLS.C3.Prop121.Card7H1
public import CFSG.GH74.GLS.C3.Layer2.NumMoved
public meta import CFSG.GH74.GLS.C3.Layer2.NumMoved
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public meta import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.GH74.GLS.C3.Prop121.Card7.Syl

open Subgroup Equiv Perm CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Prop121.Card7.HC
@[expose] def D8L : List P11 :=
  let a : P11 := PS 0 2
  let b : P11 := PS 4 6
  let c : P11 := PS 0 4 * PS 2 6
  [1, a, b, a * b, c, a * c, b * c, a * b * c]

@[expose] def SL : List P11 :=
  (flipsL.flatMap fun f => D8L.flatMap fun s => [(1 : P11), swap 8 9].map fun t => f * s * t).filter
    fun σ => decide (sign σ = 1)

end CFSG.GH74.GLS.C3.Prop121.Card7.Syl
