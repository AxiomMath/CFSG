module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow

public section

namespace CFSG.EvenSporadicStandard.Induction.Balance.Cocode24

open Equiv

abbrev Word : Type := Fin 24 → ZMod 2

abbrev Syn : Type := Fin 12 → ZMod 2

@[expose] def rowMask : Fin 12 → ℕ :=
  ![7684609, 12206594, 3113476, 14451208, 5742608, 10969120, 11641408, 5137024, 12829440,
    15377408, 14247936, 3993600]

@[expose] def pivot : Fin 12 → Fin 24 := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 10, 11, 12]

@[expose] def col (i : Fin 24) : Syn := fun k => if (rowMask k).testBit i then 1 else 0

@[expose] def synd : Word →ₗ[ZMod 2] Syn :=
  ∑ i, (LinearMap.proj i : Word →ₗ[ZMod 2] ZMod 2).smulRight (col i)

theorem synd_apply (v : Word) : synd v = ∑ i, v i • col i := by
  simp [synd, LinearMap.sum_apply]

@[expose] def golay : Submodule (ZMod 2) Word := LinearMap.ker synd

theorem mem_golay_iff (v : Word) : v ∈ golay ↔ ∑ i, v i • col i = 0 := by
  rw [golay, LinearMap.mem_ker, synd_apply]

theorem col_pivot (j : Fin 12) : col (pivot j) = Pi.single j 1 := by
  revert j
  decide

theorem col_injective : Function.Injective col := by
  intro i j h
  revert h
  revert i j
  decide

theorem synd_single (i : Fin 24) : synd (Pi.single i 1) = col i := by
  rw [synd_apply]
  simp [Pi.single_apply]

theorem synd_surjective : Function.Surjective synd := by
  intro s
  refine ⟨∑ j, s j • Pi.single (pivot j) 1, ?_⟩
  simp only [map_sum, map_smul, synd_single, col_pivot]
  ext k
  simp [Finset.sum_apply, Pi.single_apply]

end CFSG.EvenSporadicStandard.Induction.Balance.Cocode24
