
module

public import CFSG.GH74.GLS.C3.Layer2.L5C5bBase
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

public section

namespace CFSG.GH74.GLS.C3.Layer2.L5

open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model
@[expose] def conjI (h a : Nat) : Nat :=
  mt0.getD (mt0.getD (h * 128 + a) 0 * 128 + inv0.getD h 0) 0

@[expose] def gI : List Nat := [1, 4, 24]

@[expose] def bfsWordsGo (gs : List Nat) :
    Nat → Array (Option (List Nat)) → List Nat → Array (Option (List Nat))
  | 0, W, _ => W
  | fuel + 1, W, frontier =>
    let st := frontier.foldl (fun (st : Array (Option (List Nat)) × List Nat) g =>
      (List.range gs.length).foldl (fun (st : Array (Option (List Nat)) × List Nat) k =>
        let p := mt0.getD (g * 128 + gs.getD k 0) 0
        match st.1.getD p none with
        | some _ => st
        | none => (st.1.set! p (some ((st.1.getD g none).getD [] ++ [k])), st.2 ++ [p])) st) (W, [])
    bfsWordsGo gs fuel st.1 st.2

@[expose, irreducible] def Wd : Array (List Nat) :=
  (bfsWordsGo gI 128 ((Array.replicate 128 none).set! 0 (some [])) [0]).map fun o => o.getD []

@[expose] def wdChk : Bool :=
  gI.all (fun n => decide (n < 128)) &&
    (List.range 128).all fun i =>
      decide (evI gI (Wd.getD i []) = i) && (Wd.getD i []).all fun k => decide (k < 3)

@[expose, irreducible] def relsL : List (List Nat × List Nat) :=
  (((List.range 128).flatMap fun g => (List.range 3).filterMap fun k =>
    let p := mt0.getD (g * 128 + gI.getD k 0) 0
    let w1 := Wd.getD g [] ++ [k]
    let w2 := Wd.getD p []
    if w1 == w2 then none else some (w1, w2)).mergeSort
      fun a b => decide (a.1.length + a.2.length ≤ b.1.length + b.2.length))

@[expose] def relsChk : Bool :=
  relsL.all fun r => decide (evI gI r.1 = evI gI r.2)

@[expose] def xsData : List (List Nat) := [[1, 16, 7], [1, 16, 7], [1, 48, 39], [1, 48, 39]]

@[expose] def ssData : List Nat := [0, 32, 0, 32]

@[expose] def gamArr (x : List Nat) : Array Nat :=
  ((List.range 128).map fun j => evI x (Wd.getD j [])).toArray

@[expose] def invArr (t : Array Nat) : Array Nat :=
  ((List.range 128).map fun i => ((List.range 128).find? fun j => t.getD j 0 == i).getD 0).toArray

@[expose, irreducible] def gamTabs : Array (Array Nat) := (xsData.map gamArr).toArray

@[expose, irreducible] def gamInvTabs : Array (Array Nat) := (gamTabs.toList.map invArr).toArray

@[expose] def gamChk (m : Nat) : Bool :=
  let t := gamTabs.getD m #[]
  let ti := gamInvTabs.getD m #[]
  let s := ssData.getD m 0
  decide (s < 128) &&
  (List.range 128).all (fun a => decide (t.getD a 0 < 128) && decide (ti.getD a 0 < 128) &&
      decide (ti.getD (t.getD a 0) 0 = a) && decide (t.getD (ti.getD a 0) 0 = a)) &&
  (List.range 128).all (fun a => (List.range 128).all fun b =>
      decide (t.getD (mt0.getD (a * 128 + b) 0) 0 = mt0.getD (t.getD a 0 * 128 + t.getD b 0) 0)) &&
  decide (t.getD s 0 = s) &&
  (List.range 128).all (fun a => decide (t.getD (t.getD a 0) 0 = conjI s a))

end CFSG.GH74.GLS.C3.Layer2.L5
