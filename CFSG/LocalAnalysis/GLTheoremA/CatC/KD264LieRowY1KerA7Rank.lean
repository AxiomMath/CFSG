module

public import Mathlib.LinearAlgebra.Matrix.Rank

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KA7

open Matrix

open scoped Classical

theorem rank_fromBlocks_one_zero (r s : ℕ) (R : Type) [Field R] :
    (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) R) 0 0
      (0 : Matrix (Fin s) (Fin s) R)).rank = r := by
  have hdiag : Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) R) 0 0
      (0 : Matrix (Fin s) (Fin s) R) = Matrix.diagonal (Sum.elim (fun _ => (1 : R)) (fun _ => 0)) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [Matrix.one_apply, Matrix.diagonal_apply]
  rw [hdiag, Matrix.rank_diagonal, Fintype.card_subtype]
  have hset : (Finset.univ.filter fun x : Fin r ⊕ Fin s =>
      Sum.elim (fun _ => (1 : R)) (fun _ => 0) x ≠ 0) = Finset.univ.map Function.Embedding.inl := by
    ext x
    rcases x with x | x <;> simp
  rw [hset, Finset.card_map, Finset.card_univ, Fintype.card_fin]

theorem rank_map_field {K L : Type} [Field K] [Field L] {m : Type} [Fintype m] [DecidableEq m]
    (f : K →+* L) (e : Matrix m m K) : (e.map f).rank = e.rank := by
  obtain ⟨V, U, ε, hV, hU, hVeU⟩ := Matrix.exists_rank_normal_form e
  have hdet : ∀ W : Matrix m m K, IsUnit W → IsUnit (W.map f).det := by
    intro W hW
    rw [Matrix.isUnit_iff_isUnit_det] at hW
    have key : (W.map f).det = f W.det := (RingHom.map_det f W).symm
    rw [key]
    exact hW.map f
  have hmul : (V.map f) * (e.map f) * (U.map f) =
      (Matrix.fromBlocks (1 : Matrix (Fin e.rank) (Fin e.rank) L) 0 0
        (0 : Matrix (Fin (Fintype.card m - e.rank)) (Fin (Fintype.card m - e.rank)) L)).submatrix ε ε := by
    rw [← Matrix.map_mul, ← Matrix.map_mul, hVeU, ← Matrix.submatrix_map, Matrix.fromBlocks_map,
      Matrix.map_one f (map_zero f) (map_one f)]
    simp only [Matrix.map_zero f (map_zero f)]
  have hrank : (e.map f).rank = ((Matrix.fromBlocks (1 : Matrix (Fin e.rank) (Fin e.rank) L) 0 0
        (0 : Matrix (Fin (Fintype.card m - e.rank)) (Fin (Fintype.card m - e.rank)) L)).submatrix
          ε ε).rank := by
    rw [← hmul, Matrix.rank_mul_eq_left_of_isUnit_det (U.map f) _ (hdet U hU),
      Matrix.rank_mul_eq_right_of_isUnit_det (V.map f) _ (hdet V hV)]
  rw [hrank, Matrix.rank_submatrix, rank_fromBlocks_one_zero]

theorem rank_conj {L : Type} [Field L] {m : Type} [Fintype m] [DecidableEq m]
    (A B A' : Matrix m m L) (hAA : A * A' = 1) : (A * B * A').rank = B.rank := by
  have h1 : A.det * A'.det = 1 := by rw [← Matrix.det_mul, hAA, Matrix.det_one]
  have hdetA : IsUnit A.det := isUnit_iff_exists_inv.mpr ⟨A'.det, h1⟩
  have hdetA' : IsUnit A'.det := isUnit_iff_exists_inv.mpr ⟨A.det, by rw [mul_comm]; exact h1⟩
  rw [Matrix.rank_mul_eq_left_of_isUnit_det A' (A * B) hdetA',
    Matrix.rank_mul_eq_right_of_isUnit_det A B hdetA]

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KA7

end
