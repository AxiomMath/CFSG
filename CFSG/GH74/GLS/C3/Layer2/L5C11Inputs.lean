module

public import CFSG.GH74.GLS.C3.Layer2.FinModelDefs

public section

namespace CFSG.GH74.GLS.C3.Layer2.L5

open Equiv Perm CFSG.GH74.GLS.C3.Layer2.Model

@[expose] def gTw : Amb 5 := (1, swap 0 1)

@[expose] def F5b (p : Amb 5) : Bool := decide (p.2 * x4 = x4 * p.2 ∧ sign p.1 = sign p.2)

end CFSG.GH74.GLS.C3.Layer2.L5
