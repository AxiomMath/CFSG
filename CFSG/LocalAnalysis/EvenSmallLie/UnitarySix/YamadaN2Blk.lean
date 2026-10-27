module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaParF2
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.Tactic.Polynomial.Basic

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaN2

open Matrix CFSG.EvenSmallLie.UnitarySix.YamadaPar

variable {n : ℕ}

theorem zmod2_add_self (a : ZMod 2) : a + a = 0 := by
  fin_cases a <;> rfl

theorem matN_add_self (X : Matrix (Fin n) (Fin n) (ZMod 2)) : X + X = 0 := by
  ext i j; exact zmod2_add_self _

@[expose] def blkN (A C : Matrix (Fin n) (Fin n) (ZMod 2)) :
    Matrix (Fin (n + n)) (Fin (n + n)) (ZMod 2) :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks A C 0 A)

theorem blkN_mul (A C A' C' : Matrix (Fin n) (Fin n) (ZMod 2)) :
    blkN A C * blkN A' C' = blkN (A * A') (A * C' + C * A') := by
  simp only [blkN, Matrix.reindex_apply]
  rw [Matrix.submatrix_mul_equiv, fromBlocks_multiply]
  simp

theorem blkN_one : blkN (1 : Matrix (Fin n) (Fin n) (ZMod 2)) 0 = 1 := by
  rw [blkN, Matrix.fromBlocks_one, Matrix.reindex_apply, Matrix.submatrix_one_equiv]

theorem blkN_cc (A C : Matrix (Fin n) (Fin n) (ZMod 2)) (i j : Fin n) :
    blkN A C (Fin.castAdd n i) (Fin.castAdd n j) = A i j := by
  simp only [blkN, Matrix.reindex_apply, Matrix.submatrix_apply, finSumFinEquiv_symm_apply_castAdd,
    fromBlocks_apply₁₁]

theorem blkN_cn (A C : Matrix (Fin n) (Fin n) (ZMod 2)) (i j : Fin n) :
    blkN A C (Fin.castAdd n i) (Fin.natAdd n j) = C i j := by
  simp only [blkN, Matrix.reindex_apply, Matrix.submatrix_apply, finSumFinEquiv_symm_apply_castAdd,
    finSumFinEquiv_symm_apply_natAdd, fromBlocks_apply₁₂]

theorem blkN_nc (A C : Matrix (Fin n) (Fin n) (ZMod 2)) (i j : Fin n) :
    blkN A C (Fin.natAdd n i) (Fin.castAdd n j) = 0 := by
  simp only [blkN, Matrix.reindex_apply, Matrix.submatrix_apply, finSumFinEquiv_symm_apply_castAdd,
    finSumFinEquiv_symm_apply_natAdd, fromBlocks_apply₂₁, Matrix.zero_apply]

theorem blkN_nn (A C : Matrix (Fin n) (Fin n) (ZMod 2)) (i j : Fin n) :
    blkN A C (Fin.natAdd n i) (Fin.natAdd n j) = A i j := by
  simp only [blkN, Matrix.reindex_apply, Matrix.submatrix_apply, finSumFinEquiv_symm_apply_natAdd,
    fromBlocks_apply₂₂]

theorem blkN_mulVec_append (A C : Matrix (Fin n) (Fin n) (ZMod 2)) (u v : Fin n → ZMod 2) :
    blkN A C *ᵥ Fin.append u v = Fin.append (A *ᵥ u + C *ᵥ v) (A *ᵥ v) := by
  ext r
  refine Fin.addCases (fun i => ?_) (fun i => ?_) r
  · rw [Fin.append_left, mulVec, dotProduct, Fin.sum_univ_add]
    simp only [blkN_cc, blkN_cn, Fin.append_left, Fin.append_right, Pi.add_apply, mulVec,
      dotProduct]
  · rw [Fin.append_right, mulVec, dotProduct, Fin.sum_univ_add]
    simp only [blkN_nc, blkN_nn, Fin.append_left, Fin.append_right, zero_mul,
      Finset.sum_const_zero, zero_add, mulVec, dotProduct]

@[expose] def rhoN (A : Matrix (Fin n) (Fin n) (ZMod 2)) :
    Matrix (Fin (n + n)) (Fin (n + n)) (ZMod 2) := blkN A 0

@[expose] def tMN (n : ℕ) : Matrix (Fin (n + n)) (Fin (n + n)) (ZMod 2) := blkN 1 1

theorem rhoN_mul (A B : Matrix (Fin n) (Fin n) (ZMod 2)) : rhoN (A * B) = rhoN A * rhoN B := by
  simp [rhoN, blkN_mul]

theorem rhoN_one : rhoN (1 : Matrix (Fin n) (Fin n) (ZMod 2)) = 1 := blkN_one

theorem tMN_mul_tMN : tMN n * tMN n = 1 := by
  rw [tMN, blkN_mul]
  simp only [mul_one]
  rw [matN_add_self, blkN_one]

theorem blkN_one_mul_self (X : Matrix (Fin n) (Fin n) (ZMod 2)) : blkN 1 X * blkN 1 X = 1 := by
  rw [blkN_mul]
  simp only [one_mul, mul_one]
  rw [matN_add_self, blkN_one]

theorem shearN_conj (A C X : Matrix (Fin n) (Fin n) (ZMod 2)) (h : C = A * X + X * A) :
    blkN 1 X * blkN A C * blkN 1 X = rhoN A := by
  rw [blkN_mul, blkN_mul, h, rhoN]
  congr 1
  · simp
  · simp only [one_mul, mul_one]
    rw [show A * X + (A * X + X * A + X * A) = (A * X + A * X) + (X * A + X * A) by abel,
      matN_add_self, matN_add_self, add_zero]

@[expose] def bdN (A B : Matrix (Fin n) (Fin n) (ZMod 2)) :
    Matrix (Fin (n + n)) (Fin (n + n)) (ZMod 2) :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks A 0 0 B)

theorem bdN_mul (A B A' B' : Matrix (Fin n) (Fin n) (ZMod 2)) :
    bdN A B * bdN A' B' = bdN (A * A') (B * B') := by
  simp only [bdN, Matrix.reindex_apply]
  rw [Matrix.submatrix_mul_equiv, fromBlocks_multiply]
  simp

theorem bdN_one : bdN (1 : Matrix (Fin n) (Fin n) (ZMod 2)) 1 = 1 := by
  rw [bdN, Matrix.fromBlocks_one, Matrix.reindex_apply, Matrix.submatrix_one_equiv]

theorem bdN_cc (A B : Matrix (Fin n) (Fin n) (ZMod 2)) (i j : Fin n) :
    bdN A B (Fin.castAdd n i) (Fin.castAdd n j) = A i j := by
  simp only [bdN, Matrix.reindex_apply, Matrix.submatrix_apply, finSumFinEquiv_symm_apply_castAdd,
    fromBlocks_apply₁₁]

theorem bdN_cn (A B : Matrix (Fin n) (Fin n) (ZMod 2)) (i j : Fin n) :
    bdN A B (Fin.castAdd n i) (Fin.natAdd n j) = 0 := by
  simp only [bdN, Matrix.reindex_apply, Matrix.submatrix_apply, finSumFinEquiv_symm_apply_castAdd,
    finSumFinEquiv_symm_apply_natAdd, fromBlocks_apply₁₂, Matrix.zero_apply]

theorem bdN_nc (A B : Matrix (Fin n) (Fin n) (ZMod 2)) (i j : Fin n) :
    bdN A B (Fin.natAdd n i) (Fin.castAdd n j) = 0 := by
  simp only [bdN, Matrix.reindex_apply, Matrix.submatrix_apply, finSumFinEquiv_symm_apply_castAdd,
    finSumFinEquiv_symm_apply_natAdd, fromBlocks_apply₂₁, Matrix.zero_apply]

theorem bdN_nn (A B : Matrix (Fin n) (Fin n) (ZMod 2)) (i j : Fin n) :
    bdN A B (Fin.natAdd n i) (Fin.natAdd n j) = B i j := by
  simp only [bdN, Matrix.reindex_apply, Matrix.submatrix_apply, finSumFinEquiv_symm_apply_natAdd,
    fromBlocks_apply₂₂]

theorem bdN_injective_left {A B A' B' : Matrix (Fin n) (Fin n) (ZMod 2)}
    (h : bdN A B = bdN A' B') : A = A' := by
  ext i j
  have := congrFun (congrFun h (Fin.castAdd n i)) (Fin.castAdd n j)
  rwa [bdN_cc, bdN_cc] at this

theorem bdN_self (A : Matrix (Fin n) (Fin n) (ZMod 2)) : bdN A A = rhoN A := by
  ext r c
  refine Fin.addCases (fun i => ?_) (fun i => ?_) r <;>
    refine Fin.addCases (fun j => ?_) (fun j => ?_) c <;>
    simp only [bdN_cc, bdN_cn, bdN_nc, bdN_nn, rhoN, blkN_cc, blkN_cn, blkN_nc, blkN_nn,
      Matrix.zero_apply]

end CFSG.EvenSmallLie.UnitarySix.YamadaN2
