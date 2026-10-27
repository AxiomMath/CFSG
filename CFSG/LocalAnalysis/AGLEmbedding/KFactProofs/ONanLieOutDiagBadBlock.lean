module

public import Mathlib.Tactic.NoncommRing
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Data.Matrix.Mul

public section

namespace CFSG.AGLEmbedding.LieOut

open Matrix

variable {K : Type} [Field K]

@[expose] def adj {a b : Type*} (σ : K →+* K) (X : Matrix a b K) : Matrix b a K := (X.map σ)ᵀ

section Adj

variable {a b c : Type*} (σ : K →+* K)

theorem adj_mul [Fintype b] (X : Matrix a b K) (Y : Matrix b c K) :
    adj σ (X * Y) = adj σ Y * adj σ X := by
  simp [adj, Matrix.transpose_mul, Matrix.map_mul]

theorem adj_add (X Y : Matrix a b K) : adj σ (X + Y) = adj σ X + adj σ Y := by
  simp [adj, Matrix.transpose_add, Matrix.map_add]

theorem adj_sub (X Y : Matrix a b K) : adj σ (X - Y) = adj σ X - adj σ Y := by
  simp [adj, Matrix.transpose_sub, Matrix.map_sub]

theorem adj_smul (r : K) (X : Matrix a b K) : adj σ (r • X) = σ r • adj σ X := by
  ext i j
  simp [adj]

theorem adj_one [DecidableEq a] : adj σ (1 : Matrix a a K) = 1 := by
  simp [adj, Matrix.map_one _ (map_zero σ) (map_one σ)]

theorem adj_adj (hσ : ∀ c, σ (σ c) = c) (X : Matrix a b K) : adj σ (adj σ X) = X := by
  ext i j
  simp [adj, hσ]

end Adj

section Frame

variable {m k : Type*} [Fintype k] [DecidableEq m] [DecidableEq k] (σ : K →+* K)

@[expose] def frame (B : Matrix m k K) (M : Matrix k k K) : Matrix m m K :=
  1 + B * (M - 1) * adj σ B

variable {σ}

theorem frame_one (B : Matrix m k K) : frame σ B 1 = 1 := by simp [frame]

theorem frame_mul [Fintype m] {B : Matrix m k K} (hB : adj σ B * B = 1) (M N : Matrix k k K) :
    frame σ B M * frame σ B N = frame σ B (M * N) := by
  have hB' : ∀ X : Matrix k m K, adj σ B * (B * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hB, Matrix.one_mul]
  unfold frame
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
    Matrix.one_mul, Matrix.mul_assoc, hB']
  noncomm_ring

theorem frame_pow [Fintype m] {B : Matrix m k K} (hB : adj σ B * B = 1) (M : Matrix k k K)
    (j : ℕ) : frame σ B M ^ j = frame σ B (M ^ j) := by
  induction j with
  | zero => simp [frame_one]
  | succ j ih => rw [pow_succ, ih, frame_mul hB, pow_succ]

theorem adj_frame (hσ : ∀ c, σ (σ c) = c) (B : Matrix m k K) (M : Matrix k k K) :
    adj σ (frame σ B M) = frame σ B (adj σ M) := by
  unfold frame
  rw [adj_add, adj_one, adj_mul, adj_mul, adj_sub, adj_one, adj_adj σ hσ]
  simp only [Matrix.mul_assoc]

theorem adj_frame_mul_frame [Fintype m] (hσ : ∀ c, σ (σ c) = c) {B : Matrix m k K}
    (hB : adj σ B * B = 1) {M : Matrix k k K} (hM : adj σ M * M = 1) :
    adj σ (frame σ B M) * frame σ B M = 1 := by
  rw [adj_frame hσ, frame_mul hB, hM, frame_one]

theorem adj_mul_frame_mul [Fintype m] {B : Matrix m k K} (hB : adj σ B * B = 1)
    (M : Matrix k k K) : adj σ B * frame σ B M * B = M := by
  have hB' : ∀ X : Matrix k m K, adj σ B * (B * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hB, Matrix.one_mul]
  unfold frame
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
    Matrix.mul_assoc, hB, hB']
  noncomm_ring

theorem eq_one_of_frame_eq_one [Fintype m] {B : Matrix m k K} (hB : adj σ B * B = 1)
    {M : Matrix k k K} (h : frame σ B M = 1) : M = 1 := by
  rw [← adj_mul_frame_mul hB M, h, Matrix.mul_one, hB]

theorem frame_commute [Fintype m] {B : Matrix m k K} {A : Matrix m m K} {ζ : K}
    (h1 : A * B = ζ • B) (h2 : adj σ B * A = ζ • adj σ B) (M : Matrix k k K) :
    A * frame σ B M = frame σ B M * A := by
  unfold frame
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul]
  rw [← Matrix.mul_assoc A, ← Matrix.mul_assoc A, h1, Matrix.mul_assoc (B * (M - 1)), h2]
  simp only [Matrix.smul_mul, Matrix.mul_smul]

end Frame

end CFSG.AGLEmbedding.LieOut
