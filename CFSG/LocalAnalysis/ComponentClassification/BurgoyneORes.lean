module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOModel

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.O

open Matrix

variable {K : Type} [Field K]

@[expose] def pairEquiv (n : ℕ) : Fin n × Fin 2 ≃ Fin (2 * n) :=
  finProdFinEquiv.trans (finCongr (Nat.mul_comm n 2))

theorem pairEquiv_val (n : ℕ) (i : Fin n) (j : Fin 2) :
    (pairEquiv n (i, j) : ℕ) = j + 2 * i := by
  simp [pairEquiv]

variable (K) in
@[expose] def blkEquiv (n : ℕ) :
    Matrix (Fin n) (Fin n) (Matrix (Fin 2) (Fin 2) K) ≃+* Matrix (Fin (2 * n)) (Fin (2 * n)) K :=
  (Matrix.compRingEquiv (Fin n) (Fin 2) K).trans
    (Matrix.reindexAlgEquiv K K (pairEquiv n)).toRingEquiv

theorem blkEquiv_apply (n : ℕ) (M : Matrix (Fin n) (Fin n) (Matrix (Fin 2) (Fin 2) K))
    (i k : Fin n) (j l : Fin 2) :
    blkEquiv K n M (pairEquiv n (i, j)) (pairEquiv n (k, l)) = M i k j l := by
  simp [blkEquiv, Matrix.reindex_apply, Matrix.submatrix_apply]

theorem blkEquiv_transpose (n : ℕ) (M : Matrix (Fin n) (Fin n) (Matrix (Fin 2) (Fin 2) K)) :
    (blkEquiv K n M)ᵀ = blkEquiv K n (Mᵀ.map transpose) := by
  ext p q
  obtain ⟨⟨i, j⟩, rfl⟩ := (pairEquiv n).surjective p
  obtain ⟨⟨k, l⟩, rfl⟩ := (pairEquiv n).surjective q
  rw [transpose_apply, blkEquiv_apply, blkEquiv_apply]
  rfl

@[expose] def resMat {R : Type*} [Semiring R] (φ : R →+* Matrix (Fin 2) (Fin 2) K) (n : ℕ) :
    Matrix (Fin n) (Fin n) R →+* Matrix (Fin (2 * n)) (Fin (2 * n)) K :=
  (blkEquiv K n).toRingHom.comp φ.mapMatrix

theorem resMat_eq {R : Type*} [Semiring R] (φ : R →+* Matrix (Fin 2) (Fin 2) K) (n : ℕ)
    (X : Matrix (Fin n) (Fin n) R) : resMat φ n X = blkEquiv K n (X.map φ) := rfl

theorem resMat_apply {R : Type*} [Semiring R] (φ : R →+* Matrix (Fin 2) (Fin 2) K) (n : ℕ)
    (X : Matrix (Fin n) (Fin n) R) (i k : Fin n) (j l : Fin 2) :
    resMat φ n X (pairEquiv n (i, j)) (pairEquiv n (k, l)) = φ (X i k) j l := by
  rw [resMat_eq, blkEquiv_apply]
  rfl

theorem resMat_injective {R : Type*} [Semiring R] {φ : R →+* Matrix (Fin 2) (Fin 2) K}
    (hφ : Function.Injective φ) (n : ℕ) : Function.Injective (resMat φ n) := by
  intro X Y h
  ext i k
  apply hφ
  ext j l
  have := congrFun (congrFun h (pairEquiv n (i, j))) (pairEquiv n (k, l))
  rwa [resMat_apply, resMat_apply] at this

@[expose] def blkDiag (n : ℕ) (W₀ : Matrix (Fin 2) (Fin 2) K) :
    Matrix (Fin (2 * n)) (Fin (2 * n)) K :=
  blkEquiv K n (diagonal fun _ => W₀)

theorem blkDiag_apply (n : ℕ) (W₀ : Matrix (Fin 2) (Fin 2) K) (i k : Fin n) (j l : Fin 2) :
    blkDiag n W₀ (pairEquiv n (i, j)) (pairEquiv n (k, l)) = if i = k then W₀ j l else 0 := by
  rw [blkDiag, blkEquiv_apply, diagonal_apply]
  split_ifs <;> rfl

theorem blkDiag_diagonal (n : ℕ) (v : Fin 2 → K) :
    blkDiag n (diagonal v) = diagonal fun p => v ((pairEquiv n).symm p).2 := by
  ext p q
  obtain ⟨⟨i, j⟩, rfl⟩ := (pairEquiv n).surjective p
  obtain ⟨⟨k, l⟩, rfl⟩ := (pairEquiv n).surjective q
  rw [blkDiag_apply, diagonal_apply, diagonal_apply, Equiv.symm_apply_apply]
  simp only [EmbeddingLike.apply_eq_iff_eq, Prod.mk.injEq]
  by_cases hik : i = k
  · subst hik
    simp
  · simp [hik]

theorem resMat_diagonal {R : Type*} [Semiring R] (φ : R →+* Matrix (Fin 2) (Fin 2) K) (n : ℕ)
    (r : R) : resMat φ n (diagonal fun _ => r) = blkDiag n (φ r) := by
  rw [resMat_eq, blkDiag]
  congr 1
  ext i k
  simp only [map_apply, diagonal_apply]
  split_ifs <;> simp

theorem resMat_transpose_mul {R : Type*} [CommRing R] (φ : R →+* Matrix (Fin 2) (Fin 2) K)
    (σ : R →+* R) {W₀ : Matrix (Fin 2) (Fin 2) K} (hφ : ∀ x, (φ x)ᵀ * W₀ = W₀ * φ (σ x))
    (n : ℕ) (X : Matrix (Fin n) (Fin n) R) :
    (resMat φ n X)ᵀ * blkDiag n W₀ = blkDiag n W₀ * resMat φ n ((X.map σ)ᵀ) := by
  rw [resMat_eq, resMat_eq, blkEquiv_transpose, blkDiag, ← map_mul, ← map_mul]
  congr 1
  ext i k : 1
  rw [mul_diagonal, diagonal_mul]
  simp only [transpose_apply, map_apply]
  exact hφ _

theorem exists_resMat_of_commute {R : Type*} [Semiring R] (φ : R →+* Matrix (Fin 2) (Fin 2) K)
    {j : Matrix (Fin 2) (Fin 2) K} (hcomm : ∀ M : Matrix (Fin 2) (Fin 2) K, M * j = j * M →
      ∃ x, φ x = M) {n : ℕ} {h : Matrix (Fin (2 * n)) (Fin (2 * n)) K}
    (hh : h * blkDiag n j = blkDiag n j * h) : ∃ Y, resMat φ n Y = h := by
  set M := (blkEquiv K n).symm h with hM
  have hhM : h = blkEquiv K n M := by rw [hM, RingEquiv.apply_symm_apply]
  rw [hhM, blkDiag, ← map_mul, ← map_mul] at hh
  have hh' := (blkEquiv K n).injective hh
  have hblk : ∀ i k, M i k * j = j * M i k := by
    intro i k
    have := congrFun (congrFun hh' i) k
    rwa [mul_diagonal, diagonal_mul] at this
  choose Y hY using fun i k => hcomm (M i k) (hblk i k)
  refine ⟨Matrix.of Y, ?_⟩
  rw [hhM, resMat_eq]
  congr 1
  ext i k : 1
  exact hY i k

variable (K) in
abbrev kronI (n : ℕ) : Matrix (Fin n) (Fin n) K →+* Matrix (Fin (2 * n)) (Fin (2 * n)) K :=
  resMat (algebraMap K (Matrix (Fin 2) (Fin 2) K)) n

theorem kronI_apply (n : ℕ) (X : Matrix (Fin n) (Fin n) K) (i k : Fin n) (j l : Fin 2) :
    kronI K n X (pairEquiv n (i, j)) (pairEquiv n (k, l)) = if j = l then X i k else 0 := by
  rw [resMat_apply, Algebra.algebraMap_eq_smul_one, Matrix.smul_apply, one_apply, smul_eq_mul]
  split_ifs <;> simp

theorem resMat_map_algebraMap {R : Type*} [Semiring R] [Algebra K R]
    (φ : R →+* Matrix (Fin 2) (Fin 2) K)
    (hφ : ∀ a : K, φ (algebraMap K R a) = algebraMap K (Matrix (Fin 2) (Fin 2) K) a) (n : ℕ)
    (X : Matrix (Fin n) (Fin n) K) : resMat φ n (X.map (algebraMap K R)) = kronI K n X := by
  rw [resMat_eq, resMat_eq]
  congr 1
  ext i k : 1
  simp only [map_apply, hφ]

theorem trace_kronI (n : ℕ) (X : Matrix (Fin n) (Fin n) K) :
    (kronI K n X).trace = 2 * X.trace := by
  rw [Matrix.trace, Matrix.trace, ← (pairEquiv n).sum_comp, Fintype.sum_prod_type,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [diag_apply, kronI_apply, ↓reduceIte, Fin.sum_univ_two]
  ring

end CFSG.ComponentClassification.Burgoyne.O
