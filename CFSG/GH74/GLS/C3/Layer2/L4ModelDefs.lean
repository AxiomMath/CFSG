module

public import CFSG.GH74.GLS.C3.Layer2.FinModelDefs

public section

namespace CFSG.GH74.GLS.C3.Layer2.Model

open Equiv Perm Subgroup

@[expose] def vHat (n : ℕ) [NeZero n] (α : T0 n ≃* T0 n) : T0 n := x0T n * α (x0T n)

@[expose] def liftT (n : ℕ) [NeZero n] (E : Subgroup (T0 n)) : Subgroup (Amb n) :=
  E.map (T0 n).subtype

end CFSG.GH74.GLS.C3.Layer2.Model
