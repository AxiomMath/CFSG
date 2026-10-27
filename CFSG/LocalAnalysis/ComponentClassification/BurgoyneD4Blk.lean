module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOKronFix

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.D4

open Matrix CFSG
open CFSG.ComponentClassification.Burgoyne.O

variable {K : Type} {n : ℕ}

@[expose] def blkVec (u : Fin n → Fin 2 → K) : Fin (2 * n) → K :=
  fun p => u ((pairEquiv n).symm p).1 ((pairEquiv n).symm p).2

theorem blkVec_apply (u : Fin n → Fin 2 → K) (i : Fin n) (j : Fin 2) :
    blkVec u (pairEquiv n (i, j)) = u i j := by
  simp [blkVec]

@[expose] def blkOf (v : Fin (2 * n) → K) : Fin n → Fin 2 → K :=
  fun i j => v (pairEquiv n (i, j))

theorem blkVec_blkOf (v : Fin (2 * n) → K) : blkVec (blkOf v) = v := by
  funext p
  obtain ⟨⟨i, j⟩, rfl⟩ := (pairEquiv n).surjective p
  rw [blkVec_apply, blkOf]

theorem blkOf_blkVec (u : Fin n → Fin 2 → K) : blkOf (blkVec u) = u := by
  funext i j
  rw [blkOf, blkVec_apply]

theorem sum_pair {M : Type*} [AddCommMonoid M] (f : Fin (2 * n) → M) :
    ∑ p, f p = ∑ i : Fin n, ∑ j : Fin 2, f (pairEquiv n (i, j)) := by
  rw [← (pairEquiv n).sum_comp, Fintype.sum_prod_type]

variable [Field K]

@[expose] def blkDiagF (f : Fin n → Matrix (Fin 2) (Fin 2) K) :
    Matrix (Fin (2 * n)) (Fin (2 * n)) K :=
  blkEquiv K n (diagonal f)

theorem blkDiagF_apply (f : Fin n → Matrix (Fin 2) (Fin 2) K) (i k : Fin n) (j l : Fin 2) :
    blkDiagF f (pairEquiv n (i, j)) (pairEquiv n (k, l)) = if i = k then f i j l else 0 := by
  rw [blkDiagF, blkEquiv_apply, diagonal_apply]
  split_ifs <;> rfl

theorem blkDiagF_mul (f g : Fin n → Matrix (Fin 2) (Fin 2) K) :
    blkDiagF f * blkDiagF g = blkDiagF fun i => f i * g i := by
  rw [blkDiagF, blkDiagF, blkDiagF, ← map_mul, diagonal_mul_diagonal]

theorem blkDiag_eq (W₀ : Matrix (Fin 2) (Fin 2) K) : blkDiag n W₀ = blkDiagF fun _ => W₀ := rfl

theorem resMat_diagonal_eq {R : Type*} [Semiring R] (φ : R →+* Matrix (Fin 2) (Fin 2) K)
    (w : Fin n → R) : resMat φ n (diagonal w) = blkDiagF fun i => φ (w i) := by
  rw [resMat_eq, blkDiagF]
  congr 1
  ext i k : 1
  rw [map_apply, diagonal_apply, diagonal_apply]
  split_ifs <;> simp

theorem blkDiagF_mulVec (f : Fin n → Matrix (Fin 2) (Fin 2) K) (u : Fin n → Fin 2 → K) :
    blkDiagF f *ᵥ blkVec u = blkVec fun i => f i *ᵥ u i := by
  funext p
  obtain ⟨⟨i, j⟩, rfl⟩ := (pairEquiv n).surjective p
  rw [blkVec_apply, mulVec, dotProduct, sum_pair]
  simp only [blkDiagF_apply, blkVec_apply, ite_mul, zero_mul]
  rw [Finset.sum_eq_single i]
  · simp [mulVec, dotProduct]
  · intro k _ hk
    simp [Ne.symm hk]
  · simp

theorem dot_blkDiagF (f : Fin n → Matrix (Fin 2) (Fin 2) K) (u u' : Fin n → Fin 2 → K) :
    blkVec u ⬝ᵥ blkDiagF f *ᵥ blkVec u' = ∑ i, u i ⬝ᵥ f i *ᵥ u' i := by
  rw [blkDiagF_mulVec, dotProduct, sum_pair]
  simp only [blkVec_apply]
  rfl

theorem kronI_mulVec_blkVec (X : Matrix (Fin n) (Fin n) K) (u : Fin n → Fin 2 → K) :
    kronI K n X *ᵥ blkVec u = blkVec fun i j => ∑ k, X i k * u k j := by
  funext p
  obtain ⟨⟨i, j⟩, rfl⟩ := (pairEquiv n).surjective p
  rw [blkVec_apply, mulVec, dotProduct, sum_pair]
  simp only [kronI_apply, blkVec_apply, ite_mul, zero_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_eq_single j]
  · simp
  · intro l _ hl
    simp [Ne.symm hl]
  · simp

theorem kronI_perm_mulVec (σ : Equiv.Perm (Fin n)) (v : Fin (2 * n) → K) (i : Fin n) (j : Fin 2) :
    (kronI K n (σ.permMatrix K) *ᵥ v) (pairEquiv n (i, j)) = v (pairEquiv n (σ i, j)) := by
  rw [← blkVec_blkOf v, kronI_mulVec_blkVec, blkVec_apply, blkVec_blkOf]
  simp only [permMatrix_apply', ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
    ite_true, blkOf]

end CFSG.ComponentClassification.Burgoyne.D4
