module

public import CFSG.GH74.GLS.C3.Prop121.Card7F1
public import CFSG.GH74.GLS.C3.Prop121.Card7F2
public meta import CFSG.GH74.GLS.C3.Prop121.Card7F1

public section

namespace CFSG.GH74.GLS.C3.Prop121.Card7.FF

open Subgroup Equiv Perm CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model
@[expose] def CL (u : F7) : List F7 := F7L.filter fun c => decide (c * u = u * c)

@[expose] def CXL (u : F7) : List F7 := (CL u).filter fun c => decide (XF c)

@[expose] def CYL (u : F7) : List F7 := (CL u).filter fun c => decide (YF c)

@[expose] def PL : List (F7 × F7) := CXL f0 ×ˢ CYL f0

@[expose] def powB (N : ℕ) (g x : F7) : Bool := (List.range N).any fun n => decide (g ^ n = x)

end CFSG.GH74.GLS.C3.Prop121.Card7.FF
