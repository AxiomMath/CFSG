module

public import CFSG.LinearAlgebra.DihedralPlaneAction
public import CFSG.LocalAnalysis.SectionRank.Ccomm.LinearTwo

public section

namespace CFSG.LinearAlgebra

variable {F : Type*} [Field F]

theorem sq_eq_zero_of_cube_eq_zero {N : Matrix (Fin 2) (Fin 2) F} (h : N * N * N = 0) :
    N * N = 0 := by
  have hCH := mul_self_eq_trace_smul_sub_det_smul N
  have hdet : N.det = 0 := by
    have h1 := congrArg Matrix.det h
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_zero] at h1
    have h2 : N.det ^ 3 = 0 := by rw [pow_three, ← mul_assoc]; exact h1
    exact pow_eq_zero_iff (by norm_num) |>.mp h2
  rw [hdet, zero_smul, sub_zero] at hCH
  have h2 : N.trace ^ 2 • N = 0 := by
    calc N.trace ^ 2 • N = N.trace • (N.trace • N) := by rw [sq, mul_smul]
      _ = N.trace • (N * N) := by rw [hCH]
      _ = (N.trace • N) * N := by rw [smul_mul_assoc]
      _ = N * N * N := by rw [hCH]
      _ = 0 := h
  rcases smul_eq_zero.mp h2 with h3 | h3
  · rw [hCH, (pow_eq_zero_iff (by norm_num)).mp h3, zero_smul]
  · rw [h3, mul_zero]

theorem smul_one_add_smul_pow_succ {N : Matrix (Fin 2) (Fin 2) F} (hN : N * N = 0) (x y : F)
    (k : ℕ) : (x • (1 : Matrix (Fin 2) (Fin 2) F) + y • N) ^ (k + 1) =
      x ^ (k + 1) • (1 : Matrix (Fin 2) (Fin 2) F) + (((k : F) + 1) * x ^ k * y) • N := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih]
    have expand : (x ^ (k + 1) • (1 : Matrix (Fin 2) (Fin 2) F) +
        (((k : F) + 1) * x ^ k * y) • N) * (x • 1 + y • N) =
        (x ^ (k + 1) * x) • (1 : Matrix (Fin 2) (Fin 2) F) +
          (x ^ (k + 1) * y + ((k : F) + 1) * x ^ k * y * x) • N +
          (((k : F) + 1) * x ^ k * y * y) • (N * N) := by
      simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
      module
    rw [expand, hN, smul_zero, add_zero]
    congr 2
    · ring
    · push_cast
      ring

theorem orderOf_ne_fifteen_of_charP_three [CharP F 3] (A : Matrix.SpecialLinearGroup (Fin 2) F) :
    orderOf A ≠ 15 := by
  intro hA
  have hX15 : (A : Matrix (Fin 2) (Fin 2) F) ^ 15 = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_pow, ← hA, pow_orderOf_eq_one,
      Matrix.SpecialLinearGroup.coe_one]
  have hX : ∀ m : ℕ, (A : Matrix (Fin 2) (Fin 2) F) ^ m = 1 → 15 ∣ m := by
    intro m hm
    rw [← hA]
    apply orderOf_dvd_of_pow_eq_one
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, hm, Matrix.SpecialLinearGroup.coe_one]
  set X : Matrix (Fin 2) (Fin 2) F := (A : Matrix (Fin 2) (Fin 2) F) with hXdef
  have h3 : (3 : F) = 0 := CharP.ofNat_eq_zero F 3
  have h3M : (3 : Matrix (Fin 2) (Fin 2) F) = 0 := CharP.ofNat_eq_zero _ 3
  have h2 : (2 : F) ≠ 0 := by
    intro h
    have h1 : (1 : F) = 3 - 2 := by norm_num
    rw [h3, h, sub_zero] at h1
    exact one_ne_zero h1
  have hB3 : X ^ 5 * X ^ 5 * X ^ 5 = 1 := by rw [← pow_add, ← pow_add, hX15]
  have hB1 : X ^ 5 ≠ 1 := fun h => by
    have := hX 5 h
    norm_num at this
  have hN3 : (X ^ 5 - 1) * (X ^ 5 - 1) * (X ^ 5 - 1) = 0 := by
    have key : (X ^ 5 - 1) * (X ^ 5 - 1) * (X ^ 5 - 1) =
        X ^ 5 * X ^ 5 * X ^ 5 - 1 - 3 * (X ^ 5 * X ^ 5 - X ^ 5) := by noncomm_ring
    rw [key, hB3, h3M, zero_mul, sub_zero, sub_self]
  have hN2 := sq_eq_zero_of_cube_eq_zero hN3
  have hN0 : X ^ 5 - 1 ≠ 0 := fun h => hB1 (sub_eq_zero.mp h)
  have hns : ¬ ∃ c : F, X ^ 5 - 1 = c • (1 : Matrix (Fin 2) (Fin 2) F) := by
    rintro ⟨c, hc⟩
    apply hN0
    rw [hc] at hN2 ⊢
    rw [smul_mul_smul_comm, mul_one] at hN2
    have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 0 0) hN2
    simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one,
      Matrix.zero_apply] at h00
    rw [mul_self_eq_zero.mp h00, zero_smul]
  have hcomm : (X ^ 5 - 1) * X ^ 3 = X ^ 3 * (X ^ 5 - 1) := by
    rw [sub_mul, mul_sub, one_mul, mul_one, ← pow_add, ← pow_add, add_comm]
  obtain ⟨x, y, hxy⟩ := CFSG.SectionRank.Ccomm.exists_eq_smul_one_add_smul hns hcomm
  have h5 : x ^ 5 • (1 : Matrix (Fin 2) (Fin 2) F) +
      ((((4 : ℕ) : F) + 1) * x ^ 4 * y) • (X ^ 5 - 1) = 1 := by
    have h := smul_one_add_smul_pow_succ hN2 x y 4
    rw [← hxy, ← pow_mul] at h
    rw [← h, show 3 * (4 + 1) = 15 by norm_num, hX15]
  have h5' : (x ^ 5 - 1) • (1 : Matrix (Fin 2) (Fin 2) F) +
      ((((4 : ℕ) : F) + 1) * x ^ 4 * y) • (X ^ 5 - 1) = 0 := by
    rw [sub_smul, one_smul, sub_add_eq_add_sub, h5, sub_self]
  have hb0 : (((4 : ℕ) : F) + 1) * x ^ 4 * y = 0 := by
    by_contra hne
    apply hns
    refine ⟨-((((4 : ℕ) : F) + 1) * x ^ 4 * y)⁻¹ * (x ^ 5 - 1), ?_⟩
    have h1 : ((((4 : ℕ) : F) + 1) * x ^ 4 * y) • (X ^ 5 - 1) =
        -((x ^ 5 - 1) • (1 : Matrix (Fin 2) (Fin 2) F)) := eq_neg_of_add_eq_zero_right h5'
    calc X ^ 5 - 1 = ((((4 : ℕ) : F) + 1) * x ^ 4 * y)⁻¹ •
          (((((4 : ℕ) : F) + 1) * x ^ 4 * y) • (X ^ 5 - 1)) := by
          rw [smul_smul, inv_mul_cancel₀ hne, one_smul]
      _ = (-((((4 : ℕ) : F) + 1) * x ^ 4 * y)⁻¹ * (x ^ 5 - 1)) •
          (1 : Matrix (Fin 2) (Fin 2) F) := by
          rw [h1, smul_neg, smul_smul, ← neg_smul, neg_mul]
  have ha0 : x ^ 5 = 1 := by
    rw [hb0, zero_smul, add_zero] at h5'
    have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 0 0) h5'
    simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one,
      Matrix.zero_apply] at h00
    exact sub_eq_zero.mp h00
  have hx0 : x ≠ 0 := fun h => by
    rw [h, zero_pow (by norm_num)] at ha0
    exact zero_ne_one ha0
  have h5F : ((4 : ℕ) : F) + 1 ≠ 0 := by
    have h1 : ((4 : ℕ) : F) + 1 = 3 + 2 := by push_cast; norm_num
    rw [h1, h3, zero_add]
    exact h2
  have hy : y = 0 := by
    rcases mul_eq_zero.mp hb0 with h | h
    · rcases mul_eq_zero.mp h with h' | h'
      · exact absurd h' h5F
      · exact absurd ((pow_eq_zero_iff (by norm_num)).mp h') hx0
    · exact h
  rw [hy, zero_smul, add_zero] at hxy
  have hdet : x * x = 1 := by
    have h1 := congrArg Matrix.det hxy
    rw [Matrix.det_pow, Matrix.SpecialLinearGroup.det_coe, one_pow, Matrix.det_smul,
      Matrix.det_one, mul_one, Fintype.card_fin, sq] at h1
    exact h1.symm
  have hx1 : x = 1 := by
    rcases mul_self_eq_one_iff.mp hdet with h | h
    · exact h
    · exfalso
      rw [h] at ha0
      apply h2
      have h4 : (-1 : F) ^ 5 = -1 := by norm_num
      rw [h4] at ha0
      calc (2 : F) = 1 - (-1) := by norm_num
        _ = 0 := by rw [ha0, sub_self]
  rw [hx1, one_smul] at hxy
  have := hX 3 hxy
  norm_num at this

end CFSG.LinearAlgebra
