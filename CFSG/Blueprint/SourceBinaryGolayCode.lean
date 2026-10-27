module

public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Data.ZMod.Defs
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Tactic.Bound.Init
public import Mathlib.Tactic.ContinuousFunctionalCalculus

public section

namespace CFSG.Blueprint.EvenSource

@[expose] def sourceGolayR : Fin 11 → ZMod 2 := ![1, 1, 0, 1, 1, 1, 0, 0, 0, 1, 0]

@[expose] def sourceGolayB11 : Matrix (Fin 11) (Fin 11) (ZMod 2) :=
  Matrix.of fun i j => sourceGolayR (j - i)

@[expose] def sourceGolayB12 : Matrix (Fin 12) (Fin 12) (ZMod 2) :=
  Matrix.of fun i j =>
    if hi : (i : ℕ) < 11 then
      if hj : (j : ℕ) < 11 then sourceGolayB11 ⟨i, hi⟩ ⟨j, hj⟩ else 1
    else if (j : ℕ) < 11 then 1 else 0

@[expose] def sourceGolayGenerator (i : Fin 12) : Fin 24 → ZMod 2 :=
  Fin.append (fun j : Fin 12 => if j = i then 1 else 0) (sourceGolayB12 i)

@[expose] def sourceGolayCode : Submodule (ZMod 2) (Fin 24 → ZMod 2) :=
  Submodule.span (ZMod 2) (Set.range sourceGolayGenerator)

@[expose] def sourceGolayOctads : Set (Finset (Fin 24)) :=
  {O | ∃ w ∈ sourceGolayCode, Finset.univ.filter (fun i => w i ≠ 0) = O ∧ O.card = 8}

theorem sourceGolayGenerator_eq : sourceGolayGenerator =
    ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      1, 1, 0, 1, 1, 1, 0, 0, 0, 1, 0, 1],
    ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 1, 1, 0, 1, 1, 1, 0, 0, 0, 1, 1],
    ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      1, 0, 1, 1, 0, 1, 1, 1, 0, 0, 0, 1],
    ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 0, 1],
    ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1],
    ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 1, 0, 1, 1, 0, 1, 1, 1, 1],
    ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0,
      1, 0, 0, 0, 1, 0, 1, 1, 0, 1, 1, 1],
    ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0,
      1, 1, 0, 0, 0, 1, 0, 1, 1, 0, 1, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0,
      1, 1, 1, 0, 0, 0, 1, 0, 1, 1, 0, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0,
      0, 1, 1, 1, 0, 0, 0, 1, 0, 1, 1, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0,
      1, 0, 1, 1, 1, 0, 0, 0, 1, 0, 1, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0]] := by
  decide

theorem sourceGolayGenerator_mem (i : Fin 12) : sourceGolayGenerator i ∈ sourceGolayCode :=
  Submodule.subset_span ⟨i, rfl⟩

end CFSG.Blueprint.EvenSource
