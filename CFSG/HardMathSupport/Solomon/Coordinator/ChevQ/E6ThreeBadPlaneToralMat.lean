module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeBadSingerMat

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open Matrix

section Normal

variable {K : Type*} [Field K]

theorem exists_SL_conj_offDiag_eq_zero_of_cube (hζ : ∃ ζ : K, IsPrimitiveRoot ζ 3)
    {γ : GL (Fin 3) K} {α μ : K} (hγ : (γ : Matrix (Fin 3) (Fin 3) K) ^ 3 = α • 1)
    (hμ : μ ^ 3 = α) :
    ∃ z : SpecialLinearGroup (Fin 3) K, ∀ i j, i ≠ j →
      ((SpecialLinearGroup.toGL z * γ * (SpecialLinearGroup.toGL z)⁻¹ : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) i j = 0 := by
  have hα0 : α ≠ 0 := ne_zero_of_pow_three_eq_smul hγ
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    exact hα0 (by rw [← hμ]; ring)
  set s : GL (Fin 3) K := GeneralLinearGroup.scalar (Fin 3) (Units.mk0 μ hμ0) with hs
  set γ' : GL (Fin 3) K := s⁻¹ * γ with hγ'
  have hsγ : Commute s⁻¹ γ :=
    (show Commute s γ from GeneralLinearGroup.scalar_commute _ γ).inv_left
  have hγ'3 : γ' ^ 3 = 1 := by
    rw [hγ', hsγ.mul_pow]
    apply Units.ext
    have e1 : ((s⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = Matrix.scalar (Fin 3) μ⁻¹ := by
      rw [hs, ← map_inv, GeneralLinearGroup.coe_scalar, Units.val_inv_eq_inv_val, Units.val_mk0]
    have e2 : (α • 1 : Matrix (Fin 3) (Fin 3) K) = Matrix.scalar (Fin 3) α := by
      rw [Matrix.smul_one_eq_diagonal, Matrix.scalar_apply]
    rw [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, e1, hγ, e2,
      ← map_pow, ← map_mul, Units.val_one, ← hμ, ← mul_pow, inv_mul_cancel₀ hμ0, one_pow,
      map_one]
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcommE : ∀ x ∈ Subgroup.zpowers γ', ∀ y ∈ Subgroup.zpowers γ', x * y = y * x := by
    rintro x ⟨m, rfl⟩ y ⟨n, rfl⟩
    exact (Commute.zpow_zpow_self γ' m n).eq
  have hexpE : ∀ x ∈ Subgroup.zpowers γ', x ^ 3 = 1 := by
    rintro x ⟨m, rfl⟩
    rw [← _root_.zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul,
      _root_.zpow_natCast, hγ'3, _root_.one_zpow]
  obtain ⟨P, hP⟩ := RankThree.PartOne.CTP.exists_conj_diagonal_of_exponent_prime (p := 3)
    hζ _ hcommE hexpE
  have hoff := hP γ' (Subgroup.mem_zpowers γ')
  have hPγ : ∀ i j, i ≠ j →
      ((P * γ * P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j = 0 := by
    intro i j hij
    have e : P * γ * P⁻¹ = s * (P * γ' * P⁻¹) := by
      have hγs : γ = s * γ' := by rw [hγ', mul_inv_cancel_left]
      have hsP : s * P = P * s := GeneralLinearGroup.scalar_commute _ P
      rw [hγs, ← mul_assoc P s, ← hsP]
      group
    rw [e, Units.val_mul, hs, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.diagonal_mul, hoff i j hij, mul_zero]
  exact exists_SL_conj_offDiag_eq_zero hPγ

theorem signedCycMat_pow_three : (signedCycMat : Matrix (Fin 3) (Fin 3) K) ^ 3 = 1 := by
  rw [pow_succ, signedCycMat_sq_mul]

theorem diagonal_mul_signedCycMat_pow_three (d : Fin 3 → K) :
    (diagonal d * signedCycMat : Matrix (Fin 3) (Fin 3) K) ^ 3 = (d 0 * d 1 * d 2) • 1 := by
  rw [signedCycMat, pow_succ, pow_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal_apply]
  all_goals first | ring1 | (left; ring1)

theorem exists_conj_cyclic_of_not_cube (hζ : ∃ ζ : K, IsPrimitiveRoot ζ 3)
    {γ : GL (Fin 3) K} {α : K} (hγ : (γ : Matrix (Fin 3) (Fin 3) K) ^ 3 = α • 1)
    (hnc : ∀ μ : K, μ ^ 3 ≠ α) :
    ∃ (z : SpecialLinearGroup (Fin 3) K) (d : Fin 3 → K) (k : ℕ), ¬ 3 ∣ k ∧
      ((SpecialLinearGroup.toGL z * γ * (SpecialLinearGroup.toGL z)⁻¹ : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) = diagonal d * signedCycMat ^ k := by
  obtain ⟨z, d, k, hk⟩ := exists_conj_eq_diagonal_mul_signedCycMat_pow hζ hγ
  refine ⟨z, d, k, ?_, hk⟩
  rintro ⟨m, rfl⟩
  have h3 : ((SpecialLinearGroup.toGL z * γ * (SpecialLinearGroup.toGL z)⁻¹ : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) ^ 3 = α • 1 := by
    have e : (SpecialLinearGroup.toGL z * γ * (SpecialLinearGroup.toGL z)⁻¹) ^ 3 =
        SpecialLinearGroup.toGL z * γ ^ 3 * (SpecialLinearGroup.toGL z)⁻¹ := conj_pow
    rw [← Units.val_pow_eq_pow_val, e, Units.val_mul, Units.val_mul, Units.val_pow_eq_pow_val, hγ,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, ← Units.val_mul, mul_inv_cancel,
      Units.val_one]
  rw [pow_mul, signedCycMat_pow_three, one_pow, Matrix.mul_one] at hk
  rw [hk, Matrix.diagonal_pow] at h3
  exact hnc (d 0) (by
    have := congrFun (congrFun h3 0) 0
    simpa using this)

end Normal

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
