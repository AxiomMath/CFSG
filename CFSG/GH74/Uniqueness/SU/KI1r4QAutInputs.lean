module

public import CFSG.GH74.Uniqueness.SU.SU5Models
public import CFSG.GH74.Uniqueness.SU.KI1r4QAbs
public meta import CFSG.GH74.Uniqueness.SU.SU5F4
public meta import CFSG.GH74.Uniqueness.SU.SU5Models
public meta import CFSG.GH74.Uniqueness.SU.KI1r4QAbs
public meta import Mathlib
public import Mathlib

public section

namespace CFSG.GH74.Uniqueness.SU.K.R4.Q64

open Subgroup CFSG.GH74.Uniqueness.SU.SU5 CFSG.GH74.GLS.Bg.TwoGroups
@[expose] def gen : Fin 4 → L34Syl
  | 0 => ⟨F4c.z1, F4c.z0, F4c.z0⟩
  | 1 => ⟨F4c.w, F4c.z0, F4c.z0⟩
  | 2 => ⟨F4c.z0, F4c.z1, F4c.z0⟩
  | 3 => ⟨F4c.z0, F4c.w, F4c.z0⟩

@[expose] def wordA : F4c → List (Fin 4)
  | F4c.z0 => []
  | F4c.z1 => [0]
  | F4c.w => [1]
  | F4c.w2 => [0, 1]

@[expose] def wordB : F4c → List (Fin 4)
  | F4c.z0 => []
  | F4c.z1 => [2]
  | F4c.w => [3]
  | F4c.w2 => [2, 3]

@[expose] def wordZ : F4c → List (Fin 4)
  | F4c.z0 => []
  | F4c.z1 => [0, 2, 0, 2]
  | F4c.w => [1, 2, 1, 2]
  | F4c.w2 => [0, 2, 0, 2, 1, 2, 1, 2]

@[expose] def wordOf (g : L34Syl) : List (Fin 4) :=
  wordA g.a ++ wordB g.b ++ wordZ (g.c + g.a * g.b)

@[expose] def f4l : List F4c := [F4c.z0, F4c.z1, F4c.w, F4c.w2]

@[expose] def allP : List L34Syl :=
  f4l.flatMap fun a => f4l.flatMap fun b => f4l.map fun c => ⟨a, b, c⟩

@[expose] def involList : List L34Syl := allP.filter fun g => decide (g * g = 1)

@[expose] def candList : List (Fin 4 → L34Syl) :=
  involList.flatMap fun a => (involList.filter fun b => decide (a * b = b * a)).flatMap fun b =>
    involList.flatMap fun c => (involList.filter fun d => decide (c * d = d * c)).map fun d =>
      ![a, b, c, d]

@[expose] def pairList : List (L34Syl × L34Syl) :=
  involList.flatMap fun a => (involList.filter fun b => decide (a * b = b * a)).map fun b => (a, b)

@[expose] def mkS (t : Fin 4 → L34Syl) (p : L34Syl × L34Syl) : Fin 4 → L34Syl :=
  ![p.1, p.2, evalT wordOf t p.1, evalT wordOf t p.1 * evalT wordOf t p.2]

end CFSG.GH74.Uniqueness.SU.K.R4.Q64
