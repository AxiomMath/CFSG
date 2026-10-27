
module

public import CFSG.GH74.GLS.C3.Layer2.L5C5cBase
public meta import Mathlib.GroupTheory.SpecificGroups.Alternating
public meta import CFSG.GH74.GLS.C3.Prop121.ModelFive
public meta import CFSG.GH74.GLS.C3.Prop121.ModelFiveS
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelDefs
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelEmb
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelEnum
public meta import CFSG.GH74.GLS.C3.Layer2.NumMoved
public meta import CFSG.GH74.GLS.C3.Layer2.L5Fin
public meta import CFSG.GH74.GLS.C3.Layer2.L5A1
public meta import CFSG.GH74.GLS.C3.Layer2.L5B2
public meta import CFSG.GH74.GLS.C3.Layer2.L5C0Base
public meta import CFSG.GH74.GLS.C3.Layer2.L5C5bBase
public meta import CFSG.GH74.GLS.C3.Layer2.L5C5cBase

public section

namespace CFSG.GH74.GLS.C3.Layer2.L5

open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model
@[expose, irreducible] def RIdx : List Nat :=
  (List.range 128).filter fun i => decide (Sh0L.getD i 1 ∈ RhatL0)

@[expose, irreducible] def invL : List Nat :=
  (List.range 128).filter fun i => decide (mt0.getD (i * 128 + i) 0 = 0)

@[expose] def zc : Nat := 32

@[expose] def genChk : Bool :=
  (List.range 3).all (fun k => decide (mt0.getD (gI.getD k 0 * 128 + gI.getD k 0) 0 = 0)) &&
    decide (zc ≠ 0) && decide (zc < 128)

@[expose] def autPairOK (x : List Nat) (u : Nat) : Bool :=
  decide (evI x (Wd.getD u []) = u) &&
    (List.range 3).all fun k =>
      decide (evI x (Wd.getD (x.getD k 0) []) = conjI u (gI.getD k 0))

@[expose] def twistOK (x : List Nat) (u : Nat) : Bool :=
  (List.range 4).any fun m => (List.range 128).any fun h0 =>
    (List.range 3).all (fun k => decide (conjI h0 (x.getD k 0) = (xsData.getD m []).getD k 0)) &&
      decide (mt0.getD (mt0.getD (h0 * 128 + evI x (Wd.getD h0 [])) 0 * 128 + u) 0 =
        ssData.getD m 0)

@[expose] def classifyChk : Bool :=
  invL.all fun x0 => invL.all fun x1 => invL.all fun x2 =>
    decide (evI [x0, x1, x2] (Wd.getD zc []) = 0) ||
    !(relsL.all fun r => decide (evI [x0, x1, x2] r.1 = evI [x0, x1, x2] r.2)) ||
    !(RIdx.any fun r => !decide (evI [x0, x1, x2] (Wd.getD r []) ∈ RIdx)) ||
    (List.range 128).all fun u => !(autPairOK [x0, x1, x2] u) || twistOK [x0, x1, x2] u

@[expose] def gamGenChk : Bool :=
  (List.range 4).all fun m => (List.range 3).all fun k =>
    decide ((gamTabs.getD m #[]).getD (gI.getD k 0) 0 = (xsData.getD m []).getD k 0)

end CFSG.GH74.GLS.C3.Layer2.L5
