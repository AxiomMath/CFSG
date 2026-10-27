module

public import CFSG.LieType.SeitzGeneration.NonabLift

public section

namespace CFSG.LieType.SeitzGeneration

open Matrix
open scoped commutatorElement

variable {F : Type*} [Field F] {n : ℕ}

theorem smul_one_inj (hn : 0 < n) {c₁ c₂ : F}
    (h : c₁ • (1 : Matrix (Fin n) (Fin n) F) = c₂ • 1) : c₁ = c₂ := by
  have := congrFun (congrFun h ⟨0, hn⟩) ⟨0, hn⟩
  simpa using this

theorem mem_center_of_scalar {z : SpecialLinearGroup (Fin n) F} {μ : F}
    (hz : (z : Matrix (Fin n) (Fin n) F) = μ • (1 : Matrix (Fin n) (Fin n) F)) :
    z ∈ Subgroup.center (SpecialLinearGroup (Fin n) F) := by
  refine Matrix.SpecialLinearGroup.mem_center_iff.2 ⟨μ, ?_, ?_⟩
  · have h1 := z.2
    rw [hz, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at h1
    rw [Fintype.card_fin]
    exact h1
  · rw [hz]
    ext i j
    simp [Matrix.scalar_apply, Matrix.one_apply, Matrix.diagonal_apply]

theorem coe_ne_zero (hn : 0 < n) (x : SpecialLinearGroup (Fin n) F) :
    (x : Matrix (Fin n) (Fin n) F) ≠ 0 := by
  intro h
  have h1 := x.2
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  rw [h, Matrix.det_zero] at h1
  exact zero_ne_one h1

theorem exists_scalar_comm (hn : 0 < n) {x y : SpecialLinearGroup (Fin n) F}
    (h : ⁅x, y⁆ ∈ Subgroup.center (SpecialLinearGroup (Fin n) F)) :
    ∃ c : F, c ≠ 0 ∧
      (x : Matrix (Fin n) (Fin n) F) * y = c • ((y : Matrix (Fin n) (Fin n) F) * x) := by
  obtain ⟨c, hc0, hcc⟩ := exists_scalar_of_mem_center hn h
  refine ⟨c, hc0, ?_⟩
  have h1 : (⁅x, y⁆ : SpecialLinearGroup (Fin n) F) * (y * x) = x * y := by
    simp only [commutatorElement_def]; group
  have h2 := congrArg Subtype.val h1
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hcc,
    Matrix.smul_mul, Matrix.one_mul] at h2
  exact h2.symm

theorem pow_mul_quasi {A B : Matrix (Fin n) (Fin n) F} {a : F} (h : A * B = a • (B * A))
    (k : ℕ) : A ^ k * B = a ^ k • (B * A ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc A ^ (k + 1) * B = A * (A ^ k * B) := by rw [pow_succ', Matrix.mul_assoc]
      _ = A * (a ^ k • (B * A ^ k)) := by rw [ih]
      _ = a ^ k • ((A * B) * A ^ k) := by rw [Matrix.mul_smul, Matrix.mul_assoc]
      _ = a ^ (k + 1) • (B * A ^ (k + 1)) := by
          rw [h, Matrix.smul_mul, smul_smul, Matrix.mul_assoc, pow_succ' A k, pow_succ a k]

theorem mul_pow_quasi {A B : Matrix (Fin n) (Fin n) F} {a : F} (h : A * B = a • (B * A))
    (k : ℕ) : A * B ^ k = a ^ k • (B ^ k * A) := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc A * B ^ (k + 1) = (A * B ^ k) * B := by rw [pow_succ, Matrix.mul_assoc]
      _ = (a ^ k • (B ^ k * A)) * B := by rw [ih]
      _ = a ^ k • (B ^ k * (A * B)) := by rw [Matrix.smul_mul, Matrix.mul_assoc]
      _ = a ^ (k + 1) • (B ^ (k + 1) * A) := by
          rw [h, Matrix.mul_smul, smul_smul, ← Matrix.mul_assoc, ← pow_succ B k, pow_succ a k]

theorem quasi_scalar_pow_eq_one {A B : Matrix (Fin n) (Fin n) F} {a c : F}
    (h : A * B = a • (B * A)) {p : ℕ} (hB : B ^ p = c • (1 : Matrix (Fin n) (Fin n) F))
    (hc : c ≠ 0) (hA : A ≠ 0) : a ^ p = 1 := by
  have h1 := mul_pow_quasi h p
  rw [hB, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.one_mul] at h1
  by_contra hne
  have h2 : (1 - a ^ p) • (c • A) = 0 := by
    rw [sub_smul, one_smul, smul_smul, ← smul_smul, ← h1, sub_self]
  rcases smul_eq_zero.1 h2 with h3 | h3
  · exact hne (sub_eq_zero.1 h3).symm
  · rcases smul_eq_zero.1 h3 with h4 | h4
    · exact hc h4
    · exact hA h4

theorem isPrimitiveRoot_of_pow_eq_one_ne_one {ζ : F} {p : ℕ} (hp : p.Prime) (h : ζ ^ p = 1)
    (h1 : ζ ≠ 1) : IsPrimitiveRoot ζ p := by
  have : Fact p.Prime := ⟨hp⟩
  have := orderOf_eq_prime h h1
  rw [← this]
  exact IsPrimitiveRoot.orderOf ζ

theorem exists_adjust {A B R₀ : Matrix (Fin n) (Fin n) F} {ζ α β : F} {p : ℕ} [NeZero p]
    (hζ : IsPrimitiveRoot ζ p) (hAB : A * B = ζ • (B * A))
    (hA : R₀ * A = α • (A * R₀)) (hB : R₀ * B = β • (B * R₀))
    (hα : α ^ p = 1) (hβ : β ^ p = 1) (hα0 : α ≠ 0) (hβ0 : β ≠ 0) :
    ∃ i j : ℕ, (R₀ * A ^ i * B ^ j) * A = A * (R₀ * A ^ i * B ^ j) ∧
      (R₀ * A ^ i * B ^ j) * B = B * (R₀ * A ^ i * B ^ j) := by
  obtain ⟨j, -, hj⟩ := hζ.eq_pow_of_pow_eq_one hα
  have hβi : β⁻¹ ^ p = 1 := by rw [inv_pow, hβ, inv_one]
  obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one hβi
  have f1 := mul_pow_quasi hAB j
  have f2 := pow_mul_quasi hAB i
  rw [hj] at f1
  rw [hi] at f2
  have hBA' : B ^ j * A = α⁻¹ • (A * B ^ j) := by
    rw [f1, smul_smul, inv_mul_cancel₀ hα0, one_smul]
  have hAR : A * R₀ = α⁻¹ • (R₀ * A) := by rw [hA, smul_smul, inv_mul_cancel₀ hα0, one_smul]
  have hBR : B * R₀ = β⁻¹ • (R₀ * B) := by rw [hB, smul_smul, inv_mul_cancel₀ hβ0, one_smul]
  have hBAi : B * A ^ i = β • (A ^ i * B) := by
    rw [f2, smul_smul, mul_inv_cancel₀ hβ0, one_smul]
  have hcomm : A ^ i * A = A * A ^ i := (Commute.self_pow A i).eq.symm
  refine ⟨i, j, ?_, ?_⟩
  · calc R₀ * A ^ i * B ^ j * A = R₀ * A ^ i * (B ^ j * A) := by simp only [Matrix.mul_assoc]
      _ = α⁻¹ • (R₀ * A ^ i * (A * B ^ j)) := by rw [hBA', Matrix.mul_smul]
      _ = α⁻¹ • (R₀ * (A ^ i * A) * B ^ j) := by simp only [Matrix.mul_assoc]
      _ = α⁻¹ • (R₀ * (A * A ^ i) * B ^ j) := by rw [hcomm]
      _ = α⁻¹ • (R₀ * A * A ^ i * B ^ j) := by simp only [Matrix.mul_assoc]
      _ = (A * R₀) * A ^ i * B ^ j := by rw [hAR, Matrix.smul_mul, Matrix.smul_mul]
      _ = A * (R₀ * A ^ i * B ^ j) := by simp only [Matrix.mul_assoc]
  · symm
    calc B * (R₀ * A ^ i * B ^ j) = (B * R₀) * A ^ i * B ^ j := by simp only [Matrix.mul_assoc]
      _ = β⁻¹ • (R₀ * (B * A ^ i) * B ^ j) := by
          rw [hBR, Matrix.smul_mul, Matrix.smul_mul]; simp only [Matrix.mul_assoc]
      _ = β⁻¹ • (β • (R₀ * A ^ i * B * B ^ j)) := by
          rw [hBAi]; simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
      _ = R₀ * A ^ i * B * B ^ j := by rw [smul_smul, inv_mul_cancel₀ hβ0, one_smul]
      _ = R₀ * A ^ i * (B * B ^ j) := by simp only [Matrix.mul_assoc]
      _ = R₀ * A ^ i * (B ^ j * B) := by rw [(Commute.self_pow B j).eq]
      _ = R₀ * A ^ i * B ^ j * B := by simp only [Matrix.mul_assoc]

end CFSG.LieType.SeitzGeneration
