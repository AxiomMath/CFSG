module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotLeviFactEquivariance
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotOrthSL2
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open CFSG.LieType.Steinberg.Sp (blockMat)
open CFSG.SeitzReduction.LinearPilot (upperUnit diagUnit coe_diagUnit)
open scoped MatrixGroups

section FieldMap

variable {R : Type} [Field R] {S : Type} [Field S] {n : ℕ}

theorem blockMat_map {κ : Type*} [Fintype κ] [DecidableEq κ] (f : R →+* S) (p q : κ)
    (A : Matrix (Fin 2) (Fin 2) R) :
    (blockMat p q A).map f = blockMat p q (A.map f) := by
  ext a b
  simp only [blockMat, Matrix.map_apply, of_apply]
  split_ifs <;> simp [Matrix.one_apply, *]

theorem spFieldMap_longBlock (f : R →+* S) (k : Fin n) (A : SL(2, R)) :
    spFieldMap n f (longBlock R n k A) = longBlock S n k (SpecialLinearGroup.map f A) := by
  apply mat_injective
  rw [mat_spFieldMap, mat_longBlock, mat_longBlock, blockMat_map]
  rfl

theorem spFieldMap_shortBlock (f : R →+* S) {i j : Fin n} (hij : i ≠ j) (A : SL(2, R)) :
    spFieldMap n f (shortBlock R hij A) = shortBlock S hij (SpecialLinearGroup.map f A) := by
  apply mat_injective
  rw [mat_spFieldMap, mat_shortBlock, mat_shortBlock, ← map_inv, Matrix.fromBlocks_map,
    Matrix.map_zero _ (map_zero f), Matrix.transpose_map, blockMat_map, blockMat_map]
  rfl

end FieldMap

section Torus

variable {K : Type} [Field K] {n : ℕ}

@[expose] def shortParam (i j : Fin n) (κ : Kˣ) : Fin n → Kˣ :=
  fun l => if l = i then κ else if l = j then κ⁻¹ else 1

theorem diagUnit_inv (κ : Kˣ) : (diagUnit κ)⁻¹ = diagUnit κ⁻¹ := by
  rw [inv_eq_iff_mul_eq_one]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.SpecialLinearGroup.coe_mul, coe_diagUnit, Matrix.mul_apply, Fin.sum_univ_two]

theorem shortBlock_diagUnit {i j : Fin n} (hij : i ≠ j) (κ : Kˣ) :
    shortBlock K hij (diagUnit κ) = diagSp K n (shortParam i j κ) := by
  apply mat_injective
  rw [mat_shortBlock, mat_diagSp, diagUnit_inv]
  ext a b
  rcases a with x | x <;> rcases b with y | y
  · rw [fromBlocks_apply₁₁]
    simp only [blockMat, of_apply, coe_diagUnit, diagonal_apply, diagSpEntry_inl, shortParam,
      Sum.inl.injEq]
    by_cases hx : x = i <;> by_cases hy : y = i <;> by_cases hxj : x = j <;>
      by_cases hyj : y = j <;> simp_all [Matrix.one_apply, eq_comm]
  · rw [fromBlocks_apply₁₂]
    simp
  · rw [fromBlocks_apply₂₁]
    simp
  · rw [fromBlocks_apply₂₂]
    simp only [blockMat, transpose_apply, of_apply, coe_diagUnit, diagonal_apply, diagSpEntry_inr,
      shortParam, Sum.inr.injEq]
    by_cases hx : x = i <;> by_cases hy : y = i <;> by_cases hxj : x = j <;>
      by_cases hyj : y = j <;> simp_all [Matrix.one_apply, eq_comm]

end Torus

end CFSG.SeitzReduction.SymplecticPilot
