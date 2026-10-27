module

public import CFSG.GH74.GLS.C3.Layer2.L5C2e
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
public meta import CFSG.GH74.GLS.C3.Layer2.L5C2
public meta import CFSG.GH74.GLS.C3.Layer2.L5C2a
public meta import CFSG.GH74.GLS.C3.Layer2.L5C2b
public meta import CFSG.GH74.GLS.C3.Layer2.L5C2c
public meta import CFSG.GH74.GLS.C3.Layer2.L5C2d
public meta import CFSG.GH74.GLS.C3.Layer2.L5C2e

public section

namespace CFSG.GH74.GLS.C3.Layer2.L5

open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2
  CFSG.GH74.GLS.C3.Layer2.Model

namespace Fus

@[expose] def evalWG {G : Type} [Group G] (gs : List G) (w : List Nat) : G :=
  w.foldl (fun a i => a * gs.getD i 1) 1

@[expose] def permWordsGo (gs : List (Perm (Fin 16))) :
    Nat → List Nat → List (Perm (Fin 16) × List Nat) → List (Perm (Fin 16) × List Nat) →
      List (Perm (Fin 16) × List Nat)
  | 0, _, _, acc => acc
  | fuel + 1, seen, frontier, acc =>
    match frontier with
    | [] => acc
    | _ =>
      let st := frontier.foldl
        (fun (st : List Nat × List (Perm (Fin 16) × List Nat)) pw =>
          (List.range gs.length).foldl
            (fun (st : List Nat × List (Perm (Fin 16) × List Nat)) i =>
              let q := pw.1 * gs.getD i 1
              if st.1.contains (codeP16 q) then st
              else (codeP16 q :: st.1, (q, pw.2 ++ [i]) :: st.2)) st) (seen, [])
      permWordsGo gs fuel st.1 st.2.reverse (acc ++ st.2.reverse)

@[expose] def sh1WW : List (Perm (Fin 16) × List Nat) :=
  permWordsGo sh1Gens 40 [codeP16 1] [(1, [])] [(1, [])]

end Fus

end CFSG.GH74.GLS.C3.Layer2.L5
