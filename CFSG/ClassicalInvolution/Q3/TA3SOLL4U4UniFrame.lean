module

public import CFSG.LocalAnalysis.ComponentInitial.LinearUnitaryField

public section

namespace CFSG.ClassicalInvolution.Q3.TA3.L4U4

open Matrix CFSG.LocalAnalysis.ComponentInitial

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

theorem barT_mul {m n o : Type*} [Fintype n] (X : Matrix m n K) (Y : Matrix n o K) :
    ((X * Y).map h.bar)ᵀ = (Y.map h.bar)ᵀ * (X.map h.bar)ᵀ := by
  rw [Matrix.map_mul, transpose_mul]

theorem barT_barT {m n : Type*} (X : Matrix m n K) : (((X.map h.bar)ᵀ).map h.bar)ᵀ = X := by
  ext i j
  simp [h.bar_bar]

theorem barT_one {n : Type*} [Fintype n] [DecidableEq n] :
    ((1 : Matrix n n K).map h.bar)ᵀ = 1 := by
  rw [Matrix.map_one _ (map_zero _) (map_one _), transpose_one]

theorem barT_mul_eq_one {X Y : Matrix (Fin 2) (Fin 2) K} (hXY : (X.map h.bar)ᵀ * Y = 1) :
    (Y.map h.bar)ᵀ * X = 1 := by
  have := congrArg (fun M => (M.map h.bar)ᵀ) hXY
  simpa only [barT_mul, barT_barT, barT_one] using this

noncomputable abbrev leviStar (B : Matrix (Fin 2) (Fin 2) K) : Matrix (Fin 2) (Fin 2) K :=
  ((adjugate B).map h.bar)ᵀ

theorem barT_mul_leviStar {B : Matrix (Fin 2) (Fin 2) K} (hB : B.det = 1) :
    (B.map h.bar)ᵀ * leviStar h B = 1 := by
  rw [leviStar, ← barT_mul, adjugate_mul, hB, one_smul, barT_one]

theorem leviStar_mul_barT {B : Matrix (Fin 2) (Fin 2) K} (hB : B.det = 1) :
    leviStar h B * (B.map h.bar)ᵀ = 1 := by
  rw [leviStar, ← barT_mul, mul_adjugate, hB, one_smul, barT_one]

theorem det_leviStar {B : Matrix (Fin 2) (Fin 2) K} (hB : B.det = 1) : (leviStar h B).det = 1 := by
  rw [leviStar, det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det, det_adjugate, hB,
    one_pow, map_one]

theorem barT_leviStar (B : Matrix (Fin 2) (Fin 2) K) :
    (((leviStar h B).map h.bar)ᵀ) = adjugate B :=
  barT_barT h _

variable {h} in
theorem toBlocks₁₂_eq_zero_of_comm {l : K} (hl : 2 * l ≠ 0)
    {M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K}
    (hM : M * fromBlocks (l • 1) 0 0 ((-l) • 1) = fromBlocks (l • 1) 0 0 ((-l) • 1) * M) :
    M.toBlocks₁₂ = 0 ∧ M.toBlocks₂₁ = 0 := by
  rw [← fromBlocks_toBlocks M, fromBlocks_multiply, fromBlocks_multiply] at hM
  obtain ⟨-, h12, h21, -⟩ := fromBlocks_inj.mp hM
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul] at h12 h21
  refine ⟨?_, ?_⟩
  · have : (2 * l) • M.toBlocks₁₂ = 0 := by
      rw [mul_smul, two_smul, ← sub_eq_zero.mpr h12.symm, neg_smul]; abel
    exact (smul_eq_zero.mp this).resolve_left hl
  · have : (2 * l) • M.toBlocks₂₁ = 0 := by
      rw [mul_smul, two_smul, ← sub_eq_zero.mpr h21, neg_smul]; abel
    exact (smul_eq_zero.mp this).resolve_left hl

variable {h} in
theorem toBlocks₁₁_eq_zero_of_anticomm {l : K} (hl : 2 * l ≠ 0)
    {M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K}
    (hM : M * fromBlocks (l • 1) 0 0 ((-l) • 1) = -(fromBlocks (l • 1) 0 0 ((-l) • 1) * M)) :
    M.toBlocks₁₁ = 0 ∧ M.toBlocks₂₂ = 0 := by
  rw [← fromBlocks_toBlocks M, fromBlocks_multiply, fromBlocks_multiply, fromBlocks_neg] at hM
  obtain ⟨h11, -, -, h22⟩ := fromBlocks_inj.mp hM
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul] at h11 h22
  refine ⟨?_, ?_⟩
  · have : (2 * l) • M.toBlocks₁₁ = 0 := by
      rw [mul_smul, two_smul]; nth_rw 2 [h11]; abel
    exact (smul_eq_zero.mp this).resolve_left hl
  · rw [neg_smul, neg_neg] at h22
    have : (2 * l) • M.toBlocks₂₂ = 0 := by
      rw [mul_smul, two_smul]; nth_rw 1 [← h22]; abel
    exact (smul_eq_zero.mp this).resolve_left hl

theorem star_mul_eq_one_of_diag {P S : Matrix (Fin 2) (Fin 2) K}
    (hM : ((fromBlocks P 0 0 S).map h.bar)ᵀ * fromBlocks 0 1 1 0 * fromBlocks P 0 0 S =
      fromBlocks 0 1 1 0) : (P.map h.bar)ᵀ * S = 1 := by
  rw [fromBlocks_map, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply] at hM
  simp only [Matrix.map_zero _ (map_zero h.bar), transpose_zero, Matrix.zero_mul, Matrix.mul_zero,
    add_zero, zero_add, Matrix.mul_one] at hM
  exact (fromBlocks_inj.mp hM).2.1

theorem star_mul_eq_one_of_anti {Q R : Matrix (Fin 2) (Fin 2) K}
    (hM : ((fromBlocks 0 Q R 0).map h.bar)ᵀ * fromBlocks 0 1 1 0 * fromBlocks 0 Q R 0 =
      fromBlocks 0 1 1 0) : (R.map h.bar)ᵀ * Q = 1 := by
  rw [fromBlocks_map, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply] at hM
  simp only [Matrix.map_zero _ (map_zero h.bar), transpose_zero, Matrix.zero_mul, Matrix.mul_zero,
    add_zero, zero_add, Matrix.mul_one] at hM
  exact (fromBlocks_inj.mp hM).2.1

theorem exists_levi_conj_diag {P S : Matrix (Fin 2) (Fin 2) K} (hPS : (P.map h.bar)ᵀ * S = 1)
    {B : Matrix (Fin 2) (Fin 2) K} (hB : B.det = 1) :
    ∃ B' : Matrix (Fin 2) (Fin 2) K, B'.det = 1 ∧
      fromBlocks P 0 0 S * fromBlocks B 0 0 (leviStar h B) =
        fromBlocks B' 0 0 (leviStar h B') * fromBlocks P 0 0 S := by
  have hSP : (S.map h.bar)ᵀ * P = 1 := barT_mul_eq_one h hPS
  have hPS' : P * (S.map h.bar)ᵀ = 1 := mul_eq_one_comm.mp hSP
  set B' := P * B * (S.map h.bar)ᵀ with hB'
  have hdet : B'.det = 1 := by
    rw [hB', det_mul, det_mul, mul_right_comm, ← det_mul, hPS', det_one, one_mul, hB]
  have hB't : (B'.map h.bar)ᵀ = S * (B.map h.bar)ᵀ * (P.map h.bar)ᵀ := by
    rw [hB', barT_mul, barT_mul, barT_barT, Matrix.mul_assoc]
  have h1 : leviStar h B' * S * (B.map h.bar)ᵀ = S := by
    calc leviStar h B' * S * (B.map h.bar)ᵀ =
          leviStar h B' * S * (B.map h.bar)ᵀ * ((P.map h.bar)ᵀ * S) := by rw [hPS, Matrix.mul_one]
      _ = leviStar h B' * (B'.map h.bar)ᵀ * S := by
          rw [hB't]; simp only [Matrix.mul_assoc]
      _ = S := by rw [leviStar_mul_barT h hdet, Matrix.one_mul]
  refine ⟨B', hdet, ?_⟩
  rw [fromBlocks_multiply, fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  congr 1
  · rw [hB', Matrix.mul_assoc, Matrix.mul_assoc, hSP, Matrix.mul_one]
  · calc S * leviStar h B = leviStar h B' * S * (B.map h.bar)ᵀ * leviStar h B := by rw [h1]
      _ = leviStar h B' * S * ((B.map h.bar)ᵀ * leviStar h B) := by
          simp only [Matrix.mul_assoc]
      _ = leviStar h B' * S := by rw [barT_mul_leviStar h hB, Matrix.mul_one]

theorem exists_levi_conj_anti {Q R : Matrix (Fin 2) (Fin 2) K} (hRQ : (R.map h.bar)ᵀ * Q = 1)
    {B : Matrix (Fin 2) (Fin 2) K} (hB : B.det = 1) :
    ∃ B' : Matrix (Fin 2) (Fin 2) K, B'.det = 1 ∧
      fromBlocks 0 Q R 0 * fromBlocks B 0 0 (leviStar h B) =
        fromBlocks B' 0 0 (leviStar h B') * fromBlocks 0 Q R 0 := by
  have hQR : (Q.map h.bar)ᵀ * R = 1 := barT_mul_eq_one h hRQ
  have hRQ' : Q * (R.map h.bar)ᵀ = 1 := mul_eq_one_comm.mp hRQ
  set B' := Q * leviStar h B * (R.map h.bar)ᵀ with hB'
  have hdet : B'.det = 1 := by
    rw [hB', det_mul, det_mul, mul_right_comm, ← det_mul, hRQ', det_one, one_mul,
      det_leviStar h hB]
  have hB't : (B'.map h.bar)ᵀ = R * adjugate B * (Q.map h.bar)ᵀ := by
    rw [hB', barT_mul, barT_mul, barT_barT, barT_leviStar, Matrix.mul_assoc]
  have h1 : leviStar h B' * R * adjugate B = R := by
    calc leviStar h B' * R * adjugate B =
          leviStar h B' * R * adjugate B * ((Q.map h.bar)ᵀ * R) := by rw [hQR, Matrix.mul_one]
      _ = leviStar h B' * (B'.map h.bar)ᵀ * R := by
          rw [hB't]; simp only [Matrix.mul_assoc]
      _ = R := by rw [leviStar_mul_barT h hdet, Matrix.one_mul]
  refine ⟨B', hdet, ?_⟩
  rw [fromBlocks_multiply, fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  congr 1
  · rw [hB', Matrix.mul_assoc, Matrix.mul_assoc, hRQ, Matrix.mul_one]
  · calc R * B = leviStar h B' * R * adjugate B * B := by rw [h1]
      _ = leviStar h B' * R * (adjugate B * B) := by simp only [Matrix.mul_assoc]
      _ = leviStar h B' * R := by rw [adjugate_mul, hB, one_smul, Matrix.mul_one]

end CFSG.ClassicalInvolution.Q3.TA3.L4U4
