module

public import CFSG.GH74.GLS.C3.Prop121.Card7F1
public import CFSG.GH74.GLS.C3.Layer2.FinModelEnum
public import CFSG.GH74.GLS.C3.Layer2.FinModelCard
public import Mathlib.GroupTheory.Sylow
public meta import CFSG.GH74.GLS.C3.Prop121.Card7F1
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelEnum
public meta import Mathlib.Data.List.Dedup

public section

namespace CFSG.GH74.GLS.C3.Prop121.Card7.FF

open Subgroup Equiv Perm CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model
@[expose] def XAll : List F7 := F7L.filter fun s => decide (XF s)

end CFSG.GH74.GLS.C3.Prop121.Card7.FF
