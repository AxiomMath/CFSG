module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294ODMono

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

namespace I294OD

open Matrix Module

theorem exists_monomial_matrices {K : Type*} [Field K] {p n : ℕ} [NeZero p] (hp : p.Prime)
    {ζ : K} (hζ : ∀ b : K, b ^ p ≠ ζ) {M : Matrix (Fin n) (Fin n) K}
    (hM : M ^ p = scalar (Fin n) ζ) :
    ∃ (P Q N : Matrix (Fin n) (Fin n) K) (π : Equiv.Perm (Fin n)), P * Q = 1 ∧ Q * P = 1 ∧
      M * P = P * N ∧
      ∀ s : Fin n → K, N * diagonal s = diagonal (fun i => s (π.symm i)) * N := by
  have hT : (Matrix.toLin' M) ^ p = algebraMap K (Module.End K (Fin n → K)) ζ := by
    have hc := AlgEquiv.commutes (Matrix.toLinAlgEquiv' (R := K) (n := Fin n)) ζ
    rw [show (Matrix.toLin' M) = Matrix.toLinAlgEquiv' M from rfl, ← map_pow, hM]
    exact hc
  obtain ⟨m, b, u, hb⟩ := exists_monomial_basis hp hζ hT
  have hcard : Fintype.card (Fin p × Fin m) = n := by
    rw [← Module.finrank_eq_card_basis b, Module.finrank_fin_fun]
  let e : Fin p × Fin m ≃ Fin n := Fintype.equivFinOfCardEq hcard
  let b' : Basis (Fin n) K (Fin n → K) := b.reindex e
  let P : Matrix (Fin n) (Fin n) K := (Pi.basisFun K (Fin n)).toMatrix b'
  let Q : Matrix (Fin n) (Fin n) K := b'.toMatrix (Pi.basisFun K (Fin n))
  have hPQ : P * Q = 1 := Basis.toMatrix_mul_toMatrix_flip _ _
  have hQP : Q * P = 1 := Basis.toMatrix_mul_toMatrix_flip _ _
  have hPcol : ∀ i j, P i j = b' j i := fun i j => by simp [P, Basis.toMatrix_apply]
  let π : Equiv.Perm (Fin n) :=
    e.symm.trans ((Equiv.prodCongr (Equiv.addRight (1 : Fin p)) (Equiv.refl _)).trans e)
  let u' : Fin n → K := fun j => u (e.symm j)
  have hcol : ∀ j, Matrix.toLin' M (b' j) = u' j • b' (π j) := by
    intro j
    have h1 := hb (e.symm j)
    have h2 : b' j = b (e.symm j) := by simp [b', Basis.reindex_apply]
    have h3 : b' (π j) = b ((e.symm j).1 + 1, (e.symm j).2) := by
      simp [b', Basis.reindex_apply, π]
      rfl
    rw [h2, h3]
    exact h1
  let N : Matrix (Fin n) (Fin n) K := Matrix.of fun i j => if i = π j then u' j else 0
  have hMP : M * P = P * N := by
    ext k j
    have h1 : (M * P) k j = (Matrix.toLin' M (b' j)) k := by
      rw [Matrix.toLin'_apply, Matrix.mul_apply, Matrix.mulVec, dotProduct]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [hPcol]
    rw [h1, hcol j, Matrix.mul_apply]
    simp [N, hPcol, Pi.smul_apply, mul_comm]
  refine ⟨P, Q, N, π, hPQ, hQP, hMP, fun s => ?_⟩
  ext i j
  simp only [N, Matrix.mul_apply, Matrix.of_apply, Matrix.diagonal_apply, mul_ite, mul_zero,
    ite_mul, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  by_cases h : i = π j
  · subst h
    simp [mul_comm]
  · simp [h]

end I294OD

end CFSG.LocalAnalysis.RankFourTheoremC
