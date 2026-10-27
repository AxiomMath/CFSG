module

public import CFSG.GH74.GLS.C3.Layer2.FinModelTabLemmas
public meta import Mathlib.GroupTheory.SpecificGroups.Alternating
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelDefs
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelEmb
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelEnum
public meta import CFSG.GH74.GLS.C3.Layer2.NumMoved
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelTab
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelClaim

public section

namespace CFSG.GH74.GLS.C3.Layer2.Model

open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Layer2
namespace Tab

variable {n : ℕ} [NeZero n] (t : Tab n)

@[expose] def finalPosB (a : Tbl) : Bool :=
  imp (a.get t.x0i != t.x0i) <|
  (List.finRange 64).all fun u =>
    imp (a.get u == u && (List.finRange 64).all fun i =>
        a.get (a.get i) == t.mulT (t.mulT u i) (t.inv.get u)) <|
    let X0 := t.reach a t.x0i
    let V0 := t.reach a (t.mulT t.x0i (a.get t.x0i))
    imp ((List.finRange 64).all fun i => !(X0.get i && V0.get i)) <|
    imp ((List.finRange 64).all fun i => imp (t.isQ.get i && i != t.one) (!V0.get i)) <|
    imp (t.wB a) <|
      (List.finRange 64).all fun i =>
        imp (t.isQ.get i) (decide ((t.el.get (a.get i)).2 = 1))

@[expose] def claimPosB : Bool :=
  (List.finRange 64).all fun h0 => imp (t.ok0 h0) <|
  (List.finRange 64).all fun h1 => imp (t.ok1 h0 h1) <|
  (List.finRange 64).all fun h2 => imp (t.ok2 h0 h1 h2) <|
  (List.finRange 64).all fun h3 => imp (t.ok3 h0 h1 h2 h3) <|
    let a := t.ofImages ![h0, h1, h2, h3]
    imp (t.isAutB a) (t.finalPosB a)

end Tab

end CFSG.GH74.GLS.C3.Layer2.Model
