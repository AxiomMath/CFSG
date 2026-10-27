module

public import CFSG.GH74.GLS.C3.Layer2.L5B0
public meta import Mathlib.GroupTheory.SpecificGroups.Alternating
public meta import CFSG.GH74.GLS.C3.Prop121.ModelFive
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelDefs
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelEmb
public meta import CFSG.GH74.GLS.C3.Layer2.NumMoved
public meta import CFSG.GH74.GLS.C3.Layer2.L5Fin
public meta import CFSG.GH74.GLS.C3.Layer2.L5A1

public section

namespace CFSG.GH74.GLS.C3.Layer2.L5

open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model
@[expose] def gT : Fin 3 → Amb 5 := ![f2, (swap 2 3, swap 2 3), e2]

@[expose] def evalW (g : Fin 3 → Amb 5) (w : List (Fin 3)) : Amb 5 := w.foldl (fun a i => a * g i) 1

@[expose] def Wl : List (List (Fin 3)) :=
  [[], [0], [1], [2], [0, 1], [0, 2], [1, 0], [1, 2], [2, 1], [0, 1, 0], [0, 1, 2], [0, 2, 1],
    [1, 0, 1], [1, 0, 2], [1, 2, 1], [2, 1, 0], [2, 1, 2], [0, 1, 0, 1], [0, 1, 0, 2],
    [0, 1, 2, 1], [0, 2, 1, 0], [0, 2, 1, 2], [1, 0, 1, 2], [1, 0, 2, 1], [1, 2, 1, 2],
    [2, 1, 0, 2], [0, 1, 0, 1, 2], [0, 1, 0, 2, 1], [0, 1, 2, 1, 2], [0, 2, 1, 0, 2],
    [1, 0, 2, 1, 2], [0, 1, 0, 2, 1, 2]]

@[expose] def Rels : List (List (Fin 3)) :=
  [[0, 0], [1, 1], [2, 2], [0, 2, 0, 2], [1, 0, 2, 0, 2, 1], [0, 1, 0, 1, 0, 1, 0, 1],
    [0, 1, 0, 2, 0, 2, 1, 0], [0, 1, 2, 1, 0, 1, 2, 1], [1, 0, 1, 2, 1, 0, 1, 2],
    [1, 2, 1, 2, 1, 2, 1, 2], [2, 1, 0, 2, 0, 2, 1, 2], [0, 1, 0, 1, 2, 0, 2, 1, 0, 1],
    [0, 1, 0, 1, 2, 1, 0, 1, 2, 0], [0, 1, 0, 2, 1, 0, 1, 2, 0, 1],
    [0, 1, 2, 1, 2, 0, 2, 1, 2, 1], [0, 1, 2, 1, 2, 1, 2, 1, 2, 0],
    [0, 2, 1, 0, 2, 0, 2, 1, 2, 0], [1, 0, 2, 1, 2, 1, 2, 0, 1, 2],
    [0, 1, 0, 2, 1, 2, 0, 2, 1, 2, 0, 1], [0, 1, 0, 2, 1, 2, 1, 2, 0, 1, 2, 0]]

@[expose] def xChk (x : Fin 3 → Amb 5) : Bool :=
  Rels.all (fun r => decide (evalW x r = 1)) &&
    Wl.all (fun w => imp (decide (evalW gT w ∈ Pml)) (decide (evalW x w ∈ Qml)) &&
      imp (decide (evalW gT w ∈ Qml)) (decide (evalW x w ∈ Pml)) &&
      imp (decide (evalW gT w = f1)) (decide (evalW x w ≠ f1))) &&
    (let imgs := Wl.map (evalW x)
     allT5.all fun t => imgs.any fun y => decide (y = t))

@[expose] def uChk (x : Fin 3 → Amb 5) (w : List (Fin 3)) : Bool :=
  decide (evalW x w = evalW gT w) &&
    (List.finRange 3).all fun i => Wl.any fun w' =>
      decide (evalW gT w' = x i) &&
        decide (evalW x w' = evalW gT w * gT i * (evalW gT w)⁻¹)

@[expose] def gensRel (x : Fin 3 → Amb 5) (u t₀ : Amb 5) : Bool :=
  decide (emb 5 u = emb 5 t₀ * a0perm 5 * emb 5 t₀ * a0perm 5) &&
    (List.finRange 3).all fun i => decide (emb 5 (x i) =
      emb 5 t₀ * a0perm 5 * emb 5 (gT i) * (a0perm 5)⁻¹ * (emb 5 t₀)⁻¹)

@[expose] def candChk (x : Fin 3 → Amb 5) : Bool :=
  !(xChk x) || Wl.all fun w =>
    !(decide (evalW gT w ∈ Rml)) || !(uChk x w) ||
      allT5.any fun t₀ => gensRel x (evalW gT w) t₀

@[expose] def main27 : Bool :=
  Pml.all fun xa => Qml.all fun xc => allT5.all fun xb => candChk ![xa, xb, xc]

end CFSG.GH74.GLS.C3.Layer2.L5
