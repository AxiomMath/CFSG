module

public import CFSG.GH74.GLS.C3.Prop121.Card7F1
public meta import CFSG.GH74.GLS.C3.Prop121.Card7F1

public section

namespace CFSG.GH74.GLS.C3.Prop121.Card7.FF

open Subgroup Equiv Perm CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model
@[expose] def N4L : List F7 := F7L.filter fun f => decide (XF f ∧ (f : Amb 7).2 ≠ 1)

@[expose] def I40L : List F7 := F7L.filter fun f => decide (IsInv f ∧ (f : Amb 7).2 = 1)

end CFSG.GH74.GLS.C3.Prop121.Card7.FF
