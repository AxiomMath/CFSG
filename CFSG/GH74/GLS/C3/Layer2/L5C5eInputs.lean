module

public import CFSG.GH74.GLS.C3.Layer2.L5C5d
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
public meta import CFSG.GH74.GLS.C3.Layer2.L5C0
public meta import CFSG.GH74.GLS.C3.Layer2.L5C5b
public meta import CFSG.GH74.GLS.C3.Layer2.L5C5c
public meta import CFSG.GH74.GLS.C3.Layer2.L5C5d

public section

namespace CFSG.GH74.GLS.C3.Layer2.L5

open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model
@[expose] def mul2 (m : Nat) (p q : Nat × Bool) : Nat × Bool :=
  match p.2, q.2 with
  | false, false => (mt0.getD (p.1 * 128 + q.1) 0, false)
  | false, true => (mt0.getD (p.1 * 128 + q.1) 0, true)
  | true, false => (mt0.getD (p.1 * 128 + (gamTabs.getD m #[]).getD q.1 0) 0, true)
  | true, true => (mt0.getD (mt0.getD (p.1 * 128 + (gamTabs.getD m #[]).getD q.1 0) 0 * 128 +
      ssData.getD m 0) 0, false)

@[expose] def inv2 (m : Nat) (p : Nat × Bool) : Nat × Bool :=
  match p.2 with
  | false => (inv0.getD p.1 0, false)
  | true => (mt0.getD (inv0.getD (ssData.getD m 0) 0 * 128 +
      (gamTabs.getD m #[]).getD (inv0.getD p.1 0) 0) 0, true)

@[expose] def all2 : List (Nat × Bool) :=
  (List.range 128).flatMap fun i => [(i, false), (i, true)]

@[expose] def isInv2 (m : Nat) (p : Nat × Bool) : Bool := decide (mul2 m p p = (0, false))

@[expose] def cent2 (m : Nat) (p q : Nat × Bool) : Bool := decide (mul2 m p q = mul2 m q p)

@[expose] def sh2E16Chk1 (m : Nat) : Bool :=
  all2.all fun p => !(p.2 && isInv2 m p) ||
    decide ((all2.filter fun q => isInv2 m q && cent2 m p q).length < 16)

@[expose] def sh2E16Chk2 (m : Nat) : Bool :=
  all2.all fun p => !(!p.2 && isInv2 m p && !decide (p.1 ∈ RIdx) && !decide (p.1 ∈ R1Idx)) ||
    decide ((all2.filter fun q => !q.2 && isInv2 m q && cent2 m p q).length < 16)

@[expose] def sh2MoveChk (m : Nat) : Bool :=
  (List.range 128).all fun i => R1Idx.all fun j => RIdx.any fun r =>
    decide (mul2 m (mul2 m (i, true) (r, false)) (inv2 m (i, true)) = (j, false))

end CFSG.GH74.GLS.C3.Layer2.L5
