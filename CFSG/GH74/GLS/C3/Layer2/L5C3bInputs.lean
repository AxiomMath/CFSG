module

public import CFSG.GH74.GLS.C3.Layer2.L5C3a
public meta import CFSG.GH74.GLS.C3.Layer2.L5C3a
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

public section

namespace CFSG.GH74.GLS.C3.Layer2.L5

open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model
@[expose] def gS1 : Perm (Fin 16) := List.formPerm [1, 8] * List.formPerm [2, 12] * List.formPerm [4, 7] * List.formPerm [5, 6] * List.formPerm [10, 15] * List.formPerm [11, 13]

@[expose] def gS2 : Perm (Fin 16) := List.formPerm [0, 1] * List.formPerm [2, 3] * List.formPerm [6, 13] * List.formPerm [7, 10] * List.formPerm [8, 9] * List.formPerm [12, 14]

section Words

variable {M N : Type*} [Monoid M] [Monoid N]

@[expose] def wval (gens : List M) (w : List ℕ) : M := (w.map fun i => gens.getD i 1).prod

end Words

@[expose] def wBfsRound (gens : List (Perm (Fin 16))) (tab : List (Perm (Fin 16) × List ℕ)) :
    List (Perm (Fin 16) × List ℕ) :=
  tab.foldl (fun acc pw => (gens.mapIdx fun i g => (nrm (pw.1 * g), pw.2 ++ [i])).foldl
    (fun acc2 qw => if acc2.any (fun e => e.1 == qw.1) then acc2 else acc2 ++ [qw]) acc) tab

@[expose] def wBfsTab (gens : List (Perm (Fin 16))) : ℕ → List (Perm (Fin 16) × List ℕ)
  | 0 => [(1, [])]
  | n + 1 => wBfsRound gens (wBfsTab gens n)

@[expose] def homTab (tab : List (Perm (Fin 16) × List ℕ)) (images : List (Perm (Fin 16))) : Bool :=
  let imgs := images.map nrm
  let T2 := tab.map fun e => (e.1, nrm (wval imgs e.2))
  T2.all fun e₁ => T2.all fun e₂ => T2.any fun e₃ => e₃.1 == e₁.1 * e₂.1 && e₃.2 == e₁.2 * e₂.2

@[expose] def gensS0 : List (Perm (Fin 16)) := [tr1 1, tr1 2, tr1 4, tr1 8, gS1, gS2].map nrm

@[expose] def tabS0 : List (Perm (Fin 16) × List ℕ) := wBfsTab gensS0 12

@[expose] def noCHatChk (S : List (Perm (Fin 16))) : Bool :=
  let tab := tabS0
  let S' := S.map nrm
  (tab.all fun e => decide (wval gensS0 e.2 = e.1) && decide (e.1 ∈ S')) &&
  (S'.all fun s => tab.any fun e => e.1 == s) &&
  (gensS0.all fun g => decide (g ∈ S')) &&
  (S'.all fun u₁ => S'.all fun u₂ =>
    !(homTab tab [tr1 (cHat 1), tr1 (cHat 2), tr1 (cHat 4), tr1 (cHat 8), u₁, u₂]))

end CFSG.GH74.GLS.C3.Layer2.L5
