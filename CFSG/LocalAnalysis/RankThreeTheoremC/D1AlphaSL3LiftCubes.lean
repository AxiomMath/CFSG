module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Algebra.Polynomial.SpecificDegree

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SL3Lift

open Matrix Polynomial

private theorem cayley_hamilton_three {R : Type*} [CommRing R] (A : Matrix (Fin 3) (Fin 3) R) :
    A ^ 3 - A.trace • A ^ 2 + (adjugate A).trace • A -
      A.det • (1 : Matrix (Fin 3) (Fin 3) R) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_three, Matrix.trace_fin_three,
      Matrix.adjugate_fin_three, Matrix.det_fin_three] <;> ring

set_option linter.unusedVariables false in
theorem cube_eq_one_of_conj_eq_smul {k : Type*} [Field k]
    (s : SpecialLinearGroup (Fin 3) k) (g : GL (Fin 3) k) {w : k}
    (hw : w ^ 3 = 1) (hw1 : w ≠ 1)
    (h : (g : Matrix (Fin 3) (Fin 3) k) * (s : Matrix (Fin 3) (Fin 3) k) *
        ((g⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) =
      w • (s : Matrix (Fin 3) (Fin 3) k)) :
    (s : Matrix (Fin 3) (Fin 3) k) ^ 3 = 1 := by
  set t : Matrix (Fin 3) (Fin 3) k := (s : Matrix (Fin 3) (Fin 3) k) with ht_def
  set v : Matrix (Fin 3) (Fin 3) k := (g : Matrix (Fin 3) (Fin 3) k) with hv_def
  set u : Matrix (Fin 3) (Fin 3) k := ((g⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k)
    with hu_def
  have hvu : v * u = 1 := Units.mul_inv g
  have huv : u * v = 1 := Units.inv_mul g
  have hdet : t.det = 1 := s.det_coe
  have htt : t * adjugate t = 1 := by rw [mul_adjugate, hdet, one_smul]
  have htt' : adjugate t * t = 1 := by rw [adjugate_mul, hdet, one_smul]
  have hconj : ∀ M : Matrix (Fin 3) (Fin 3) k, trace (v * M * u) = trace M := fun M => by
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, huv, Matrix.one_mul]
  have h1 : trace t = 0 := by
    have h3 := congrArg trace h
    rw [hconj, Matrix.trace_smul, smul_eq_mul] at h3
    have h2 : (1 - w) * trace t = 0 := by linear_combination h3
    rcases mul_eq_zero.1 h2 with h4 | h4
    · exact absurd (sub_eq_zero.1 h4).symm hw1
    · exact h4
  have hv1 : ∀ Y : Matrix (Fin 3) (Fin 3) k, u * (v * Y) = Y := fun Y => by
    rw [← Matrix.mul_assoc, huv, Matrix.one_mul]
  have ht1 : ∀ Y : Matrix (Fin 3) (Fin 3) k, t * (adjugate t * Y) = Y := fun Y => by
    rw [← Matrix.mul_assoc, htt, Matrix.one_mul]
  have ht2 : ∀ Y : Matrix (Fin 3) (Fin 3) k, adjugate t * (t * Y) = Y := fun Y => by
    rw [← Matrix.mul_assoc, htt', Matrix.one_mul]
  have hX : (w • t) * (v * adjugate t * u) = 1 := by
    rw [← h]
    simp only [Matrix.mul_assoc, hv1, ht1, hvu]
  have hY : adjugate t = w • (v * adjugate t * u) := by
    calc adjugate t = adjugate t * 1 := (Matrix.mul_one _).symm
      _ = adjugate t * ((w • t) * (v * adjugate t * u)) := by rw [hX]
      _ = w • (v * adjugate t * u) := by rw [Matrix.smul_mul, Matrix.mul_smul, ht2]
  have h2 : trace (adjugate t) = 0 := by
    have h3 := congrArg trace hY
    rw [Matrix.trace_smul, hconj, smul_eq_mul] at h3
    have h5 : (1 - w) * trace (adjugate t) = 0 := by linear_combination h3
    rcases mul_eq_zero.1 h5 with h4 | h4
    · exact absurd (sub_eq_zero.1 h4).symm hw1
    · exact h4
  have hCH := cayley_hamilton_three t
  rw [h1, h2, hdet] at hCH
  simp only [zero_smul, one_smul, sub_zero, add_zero] at hCH
  exact sub_eq_zero.1 hCH

theorem exists_cube_root_of_det_one {k : Type*} [Field k] (s : Matrix (Fin 3) (Fin 3) k)
    (hdet : s.det = 1) {ζ : k} (hs : s ^ 3 = ζ • (1 : Matrix (Fin 3) (Fin 3) k)) :
    ∃ η : k, η ^ 3 = ζ := by
  by_contra hno
  have hno' : ∀ η : k, η ^ 3 ≠ ζ := fun η hη => hno ⟨η, hη⟩
  have hPmonic : (X ^ 3 - C ζ : k[X]).Monic := monic_X_pow_sub_C ζ (by norm_num)
  have hPdeg : (X ^ 3 - C ζ : k[X]).natDegree = 3 := natDegree_X_pow_sub_C
  have hPirr : Irreducible (X ^ 3 - C ζ : k[X]) := by
    refine irreducible_of_degree_le_three_of_not_isRoot ?_ ?_
    · rw [hPdeg]; simp
    · intro x hx
      apply hno' x
      simpa [IsRoot, sub_eq_zero] using hx
  have hPaeval : aeval s (X ^ 3 - C ζ : k[X]) = 0 := by
    simp [hs, Algebra.algebraMap_eq_smul_one]
  have hmin := minpoly.eq_of_irreducible_of_monic hPirr hPaeval hPmonic
  have hdvd := Matrix.minpoly_dvd_charpoly s
  rw [← hmin] at hdvd
  have hχ : s.charpoly = X ^ 3 - C ζ := by
    refine eq_of_monic_of_dvd_of_natDegree_le hPmonic (Matrix.charpoly_monic s) hdvd ?_
    rw [Matrix.charpoly_natDegree_eq_dim, hPdeg]
    simp
  have h0 := Matrix.det_eq_sign_charpoly_coeff s
  rw [hχ, hdet] at h0
  simp [coeff_sub, coeff_X_pow, coeff_C] at h0
  have hζ : ζ = 1 := by linear_combination -h0
  exact hno' 1 (by rw [hζ]; norm_num)

end CFSG.LocalAnalysis.RankThreeTheoremC.SL3Lift
