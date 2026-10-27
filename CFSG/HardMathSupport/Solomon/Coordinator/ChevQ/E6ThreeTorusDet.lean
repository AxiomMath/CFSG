module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeLayerNC
public import CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.TOdd.FullLin

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open Matrix

section Det

variable {K : Type*} [Field K]

theorem toGL_conjSL_eq_mul (g : GL (Fin 3) K) (h : SpecialLinearGroup (Fin 3) K) :
    SpecialLinearGroup.toGL (conjSL g h) = g * SpecialLinearGroup.toGL h * g⁻¹ := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, SpecialLinearGroup.coe_GL_coe_matrix,
    SpecialLinearGroup.coe_GL_coe_matrix, conjSL_apply, LieType.SeitzGeneration.conjUnit_coe]

theorem exists_commute_det_eq_of_pow_three [Finite K] (h3 : 3 ∣ Nat.card K - 1)
    {γ : GL (Fin 3) K} {α : K} (hγ : (γ : Matrix (Fin 3) (Fin 3) K) ^ 3 = α • 1) (β : Kˣ) :
    ∃ δ : GL (Fin 3) K, δ * γ = γ * δ ∧ GeneralLinearGroup.det δ = β := by
  classical
  have hα0 : α ≠ 0 := ne_zero_of_pow_three_eq_smul hγ
  by_cases hcube : ∃ μ : K, μ ^ 3 = α
  · obtain ⟨μ, hμ⟩ := hcube
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
        rw [hs, ← map_inv, GeneralLinearGroup.coe_scalar, Units.val_inv_eq_inv_val,
          Units.val_mk0]
      have e2 : (α • 1 : Matrix (Fin 3) (Fin 3) K) = Matrix.scalar (Fin 3) α := by
        rw [Matrix.smul_one_eq_diagonal, Matrix.scalar_apply]
      rw [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, e1, hγ, e2,
        ← map_pow, ← map_mul, Units.val_one, ← hμ, ← mul_pow, inv_mul_cancel₀ hμ0, one_pow,
        map_one]
    obtain ⟨ω, hω⟩ := exists_isPrimitiveRoot_three h3
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hcommE : ∀ x ∈ Subgroup.zpowers γ', ∀ y ∈ Subgroup.zpowers γ', x * y = y * x := by
      rintro x ⟨m, rfl⟩ y ⟨n, rfl⟩
      exact (Commute.zpow_zpow_self γ' m n).eq
    have hexpE : ∀ x ∈ Subgroup.zpowers γ', x ^ 3 = 1 := by
      rintro x ⟨m, rfl⟩
      rw [← _root_.zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul,
        _root_.zpow_natCast, hγ'3, _root_.one_zpow]
    obtain ⟨P, hP⟩ := RankThree.PartOne.CTP.exists_conj_diagonal_of_exponent_prime (p := 3)
      ⟨ω, hω⟩ _ hcommE hexpE
    have hoff := hP γ' (Subgroup.mem_zpowers γ')
    have hDdet : (Matrix.diagonal ![(β : K), 1, 1]).det ≠ 0 := by
      simp [Matrix.det_diagonal, Fin.prod_univ_three]
    set D : GL (Fin 3) K := GeneralLinearGroup.mkOfDetNeZero _ hDdet with hD
    have hDv : (D : Matrix (Fin 3) (Fin 3) K) = Matrix.diagonal ![(β : K), 1, 1] := rfl
    have hDN : D * (P * γ' * P⁻¹) = P * γ' * P⁻¹ * D := by
      apply Units.ext
      rw [Units.val_mul D, Units.val_mul _ D]
      ext i j
      rw [hDv, Matrix.diagonal_mul, Matrix.mul_diagonal]
      by_cases hij : i = j
      · subst hij
        ring
      · rw [hoff i j hij]
        ring
    have hδ' : P⁻¹ * D * P * γ' = γ' * (P⁻¹ * D * P) := by
      calc P⁻¹ * D * P * γ' = P⁻¹ * (D * (P * γ' * P⁻¹)) * P := by group
        _ = P⁻¹ * (P * γ' * P⁻¹ * D) * P := by rw [hDN]
        _ = γ' * (P⁻¹ * D * P) := by group
    have hγs : γ = s * γ' := by rw [hγ', mul_inv_cancel_left]
    have hsδ : s * (P⁻¹ * D * P) = P⁻¹ * D * P * s := GeneralLinearGroup.scalar_commute _ _
    refine ⟨P⁻¹ * D * P, ?_, ?_⟩
    · rw [hγs]
      calc P⁻¹ * D * P * (s * γ') = P⁻¹ * D * P * s * γ' := (mul_assoc _ _ _).symm
        _ = s * (P⁻¹ * D * P) * γ' := by rw [hsδ]
        _ = s * (P⁻¹ * D * P * γ') := mul_assoc _ _ _
        _ = s * (γ' * (P⁻¹ * D * P)) := by rw [hδ']
        _ = s * γ' * (P⁻¹ * D * P) := (mul_assoc _ _ _).symm
    · rw [map_mul, map_mul, map_inv, mul_right_comm, inv_mul_cancel, one_mul]
      apply Units.ext
      rw [GeneralLinearGroup.val_det_apply, hDv, Matrix.det_diagonal, Fin.prod_univ_three]
      simp
  · have hα' : ∀ b : K, b ^ 3 ≠ α := fun b hb => hcube ⟨b, hb⟩
    have hdet : (γ : Matrix (Fin 3) (Fin 3) K).det = α := by
      have h := det_sub_smul_one_of_pow_three_not_cube hα' hγ 0
      simpa using h
    have hnc : ¬ ∃ w : Kˣ, w ^ 3 = GeneralLinearGroup.det γ := by
      rintro ⟨w, hw⟩
      apply hα' w
      have h := congrArg Units.val hw
      rwa [Units.val_pow_eq_pow_val, GeneralLinearGroup.val_det_apply, hdet] at h
    obtain ⟨k, w, hw⟩ := SeitzOuterCube.Exc.TOdd.exists_cube_mul_pow (v := β⁻¹) hnc
    refine ⟨γ ^ k * GeneralLinearGroup.scalar (Fin 3) w⁻¹, ?_, ?_⟩
    · have h1 : Commute (γ ^ k) γ := (Commute.refl γ).pow_left k
      have h2 : Commute (GeneralLinearGroup.scalar (Fin 3) w⁻¹) γ :=
        GeneralLinearGroup.scalar_commute _ γ
      exact (h1.mul_left h2).eq
    · rw [map_mul, map_pow, GeneralLinearGroup.det_scalar, Fintype.card_fin, inv_pow, hw,
        _root_.mul_inv_rev, inv_inv, mul_inv_cancel_left]

theorem exists_conjSL_mul_eq [Finite K] (h3 : 3 ∣ Nat.card K - 1) {A B : GL (Fin 3) K}
    (hAB : Commute A B) (x : SpecialLinearGroup (Fin 3) K) {α : K}
    (hx : ((B * SpecialLinearGroup.toGL x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ^ 3 =
      α • 1) :
    ∃ y : SpecialLinearGroup (Fin 3) K, conjSL A⁻¹ x * y = conjSL B⁻¹ y * x := by
  obtain ⟨δ, hδ, hdet⟩ := exists_commute_det_eq_of_pow_three h3 hx (GeneralLinearGroup.det A)
  have hy1 : ((A⁻¹ * δ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1 := by
    rw [← GeneralLinearGroup.val_det_apply, map_mul, map_inv, hdet, inv_mul_cancel,
      Units.val_one]
  obtain ⟨y, hy⟩ : ∃ y : SpecialLinearGroup (Fin 3) K, SpecialLinearGroup.toGL y = A⁻¹ * δ :=
    ⟨⟨_, hy1⟩, Units.ext rfl⟩
  refine ⟨y, SpecialLinearGroup.toGL_injective ?_⟩
  rw [map_mul, map_mul, toGL_conjSL_eq_mul, toGL_conjSL_eq_mul, hy, inv_inv, inv_inv]
  have hBA : B⁻¹ * A⁻¹ * B = A⁻¹ := by
    rw [mul_assoc, hAB.inv_left.eq, ← mul_assoc, inv_mul_cancel, one_mul]
  calc A⁻¹ * SpecialLinearGroup.toGL x * A * (A⁻¹ * δ)
      = A⁻¹ * (SpecialLinearGroup.toGL x * δ) := by group
    _ = B⁻¹ * A⁻¹ * B * (SpecialLinearGroup.toGL x * δ) := by rw [hBA]
    _ = B⁻¹ * A⁻¹ * (B * SpecialLinearGroup.toGL x * δ) := by group
    _ = B⁻¹ * A⁻¹ * (δ * (B * SpecialLinearGroup.toGL x)) := by rw [hδ]
    _ = B⁻¹ * (A⁻¹ * δ) * B * SpecialLinearGroup.toGL x := by group

end Det

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

end
