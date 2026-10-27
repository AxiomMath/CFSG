module

public import CFSG.ClassicalInvolution.Models.SymplecticPairs.ShortRoot

public section

namespace CFSG.ClassicalInvolution.Q3.Q3Z

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Steinberg.Sp (blockMat)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open scoped MatrixGroups

variable {K K' K'' : Type} [Field K] [Field K'] [Field K''] {n : ℕ}

theorem map_gram (φ : K →+* K') : (gram K n).map φ = gram K' n := by
  ext a b
  rw [Matrix.map_apply, gram_apply, gram_apply]
  split_ifs
  · rcases a with i | i <;> simp [sgn]
  · exact map_zero φ

theorem map_symplectic (φ : K →+* K') (x : StatedSp n K) :
    Matrix.transpose ((mat n K x).map φ) * gram K' n * (mat n K x).map φ = gram K' n := by
  have h := congrArg (fun M => M.map φ) (mat_transpose_mul_gram_mul x)
  simp only [Matrix.transpose_map, Matrix.map_mul, map_gram] at h
  exact h

@[expose] noncomputable def spMap (φ : K →+* K') : StatedSp n K →* StatedSp n K' where
  toFun x := ofSymplecticMat ((mat n K x).map φ) (map_symplectic φ x)
  map_one' := mat_injective (by
    rw [mat_ofSymplecticMat, map_one, map_one]
    exact Matrix.map_one φ (map_zero φ) (map_one φ))
  map_mul' x y := mat_injective (by
    rw [mat_ofSymplecticMat, map_mul, map_mul, mat_ofSymplecticMat, mat_ofSymplecticMat]
    exact Matrix.map_mul)

theorem mat_spMap (φ : K →+* K') (x : StatedSp n K) :
    mat n K' (spMap φ x) = (mat n K x).map φ :=
  mat_ofSymplecticMat ((mat n K x).map φ) (map_symplectic φ x)

theorem spMap_injective (φ : K →+* K') : Function.Injective (spMap (n := n) φ) := by
  intro x y h
  apply mat_injective
  have := congrArg (mat n K') h
  rw [mat_spMap, mat_spMap] at this
  exact Matrix.map_injective φ.injective this

theorem spMap_comp (φ : K →+* K') (ψ : K' →+* K'') (x : StatedSp n K) :
    spMap ψ (spMap φ x) = spMap (ψ.comp φ) x :=
  mat_injective (by rw [mat_spMap, mat_spMap, mat_spMap, Matrix.map_map]; rfl)

theorem spMap_surjective (e : K ≃+* K') : Function.Surjective (spMap (n := n) e.toRingHom) := by
  intro y
  refine ⟨spMap e.symm.toRingHom y, ?_⟩
  rw [spMap_comp]
  apply mat_injective
  rw [mat_spMap]
  ext i j
  simp

theorem spMap_blockMat (φ : K →+* K') {κ : Type} [DecidableEq κ] (p q : κ)
    (A : Matrix (Fin 2) (Fin 2) K) :
    (blockMat p q A).map φ = blockMat p q (A.map φ) := by
  ext a b
  simp only [Matrix.map_apply, blockMat, Matrix.of_apply]
  split_ifs <;> first | rfl | simp [Matrix.one_apply, *]

theorem spMap_longBlock (φ : K →+* K') (k : Fin n) (A : SL(2, K)) :
    spMap φ (longBlock K n k A) = longBlock K' n k (Matrix.SpecialLinearGroup.map φ A) := by
  apply mat_injective
  rw [mat_spMap, mat_longBlock, mat_longBlock, spMap_blockMat]
  rfl

theorem spMap_shortBlock (φ : K →+* K') {i j : Fin n} (hij : i ≠ j) (A : SL(2, K)) :
    spMap φ (shortBlock K hij A) = shortBlock K' hij (Matrix.SpecialLinearGroup.map φ A) := by
  apply mat_injective
  rw [mat_spMap, mat_shortBlock, mat_shortBlock, Matrix.fromBlocks_map, spMap_blockMat,
    Matrix.transpose_map, spMap_blockMat, ← map_inv (Matrix.SpecialLinearGroup.map φ) A]
  simp only [map_zero, Matrix.map_zero]
  rfl

end CFSG.ClassicalInvolution.Q3.Q3Z
