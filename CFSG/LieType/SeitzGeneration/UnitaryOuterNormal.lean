module

public import CFSG.LieType.SeitzGeneration.UnitaryBlocks
public import CFSG.LieType.SeitzGeneration.OutdiagHeis
public import CFSG.LieType.SeitzGeneration.NonabHeisThreeUnitary

public section

namespace CFSG.LieType.SeitzGeneration

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel

variable {ℓ f : ℕ} {K : Type} [Field K]

theorem gram_eq_smul_one_alpha (h : UnitaryFieldData ℓ f K) (hq3 : 3 ∣ ℓ ^ f + 1)
    {X Y P : Matrix (Fin 3) (Fin 3) K} {ω ξ α : K} (hω : IsPrimitiveRoot ω 3) (hξ : ξ ^ 3 = 1)
    (hX : (X.map h.bar)ᵀ * X = 1) (hY : (Y.map h.bar)ᵀ * Y = 1)
    (hXP : X * P = P * heisC α) (hYP : Y * P = P * diagonal ![ξ, ξ * ω, ξ * ω ^ 2]) :
    ∃ ν : K, (P.map h.bar)ᵀ * P = ν • (1 : Matrix (Fin 3) (Fin 3) K) := by
  have hbω : h.bar ω = ω ^ 2 := bar_eq_sq_of_cube h hq3 hω.pow_eq_one
  have hbξ : h.bar ξ = ξ ^ 2 := bar_eq_sq_of_cube h hq3 hξ
  have hω3 : ω ^ 3 = 1 := hω.pow_eq_one
  have hω1 : ω ≠ 1 := hω.ne_one (by norm_num)
  have hω2 : ω ^ 2 ≠ 1 := by
    intro h2
    have := hω.pow_ne_one_of_pos_of_lt (by norm_num : (2 : ℕ) ≠ 0) (by norm_num : 2 < 3)
    exact this h2
  set G := (P.map h.bar)ᵀ * P with hG
  have hGdiag : ∀ {M : Matrix (Fin 3) (Fin 3) K}, (M.map h.bar)ᵀ * M = 1 →
      ∀ {N : Matrix (Fin 3) (Fin 3) K}, M * P = P * N →
        ((P * N).map h.bar)ᵀ * (P * N) = G := fun {M} hM {N} hMN => by
    rw [← hMN, Matrix.map_mul, Matrix.transpose_mul, Matrix.mul_assoc,
      ← Matrix.mul_assoc (M.map h.bar)ᵀ, hM, Matrix.one_mul]
  have h1 := hGdiag hY hYP
  have h2 := hGdiag hX hXP
  have hdiag : ∀ d : Fin 3 → K, ((P * diagonal d).map h.bar)ᵀ * (P * diagonal d) =
      diagonal (fun k => h.bar (d k)) * G * diagonal d := fun d => by
    rw [Matrix.map_mul, Matrix.transpose_mul, Matrix.diagonal_map (map_zero h.bar),
      Matrix.diagonal_transpose, hG, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]
  have hD : ∀ k l : Fin 3, G k l = h.bar (![ξ, ξ * ω, ξ * ω ^ 2] k) *
      G k l * (![ξ, ξ * ω, ξ * ω ^ 2] l) := by
    intro k l
    have := congrFun (congrFun h1 k) l
    rw [hdiag, Matrix.mul_diagonal, Matrix.diagonal_mul] at this
    exact this.symm
  have key : ∀ (c z : K), c ≠ 1 → z = c * z → z = 0 := fun c z hc hz => by
    have : (1 - c) * z = 0 := by linear_combination hz
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 (Ne.symm hc))
  have p01 : h.bar ξ * (ξ * ω) = ω := by rw [hbξ]; linear_combination ω * hξ
  have p02 : h.bar ξ * (ξ * ω ^ 2) = ω ^ 2 := by rw [hbξ]; linear_combination ω ^ 2 * hξ
  have p10 : h.bar (ξ * ω) * ξ = ω ^ 2 := by
    rw [map_mul, hbξ, hbω]; linear_combination ω ^ 2 * hξ
  have p12 : h.bar (ξ * ω) * (ξ * ω ^ 2) = ω := by
    rw [map_mul, hbξ, hbω]; linear_combination ω ^ 4 * hξ + ω * hω3
  have p20 : h.bar (ξ * ω ^ 2) * ξ = ω := by
    rw [map_mul, hbξ, map_pow, hbω]; linear_combination ω ^ 4 * hξ + ω * hω3
  have p21 : h.bar (ξ * ω ^ 2) * (ξ * ω) = ω ^ 2 := by
    rw [map_mul, hbξ, map_pow, hbω]; linear_combination ω ^ 5 * hξ + ω ^ 2 * hω3
  have offd : ∀ (k l : Fin 3) (c : K), c ≠ 1 →
      h.bar (![ξ, ξ * ω, ξ * ω ^ 2] k) * (![ξ, ξ * ω, ξ * ω ^ 2] l) = c → G k l = 0 :=
    fun k l c hc hcl => key c _ hc (by
      calc G k l = h.bar (![ξ, ξ * ω, ξ * ω ^ 2] k) * G k l * (![ξ, ξ * ω, ξ * ω ^ 2] l) :=
            hD k l
        _ = (h.bar (![ξ, ξ * ω, ξ * ω ^ 2] k) * (![ξ, ξ * ω, ξ * ω ^ 2] l)) * G k l := by ring
        _ = c * G k l := by rw [hcl])
  have g01 : G 0 1 = 0 := offd 0 1 ω hω1 p01
  have g02 : G 0 2 = 0 := offd 0 2 (ω ^ 2) hω2 p02
  have g10 : G 1 0 = 0 := offd 1 0 (ω ^ 2) hω2 p10
  have g12 : G 1 2 = 0 := offd 1 2 ω hω1 p12
  have g20 : G 2 0 = 0 := offd 2 0 ω hω1 p20
  have g21 : G 2 1 = 0 := offd 2 1 (ω ^ 2) hω2 p21
  have h2' : ((heisC α).map h.bar)ᵀ * G * heisC α = G := by
    calc ((heisC α).map h.bar)ᵀ * G * heisC α = ((P * heisC α).map h.bar)ᵀ * (P * heisC α) := by
          rw [Matrix.map_mul, Matrix.transpose_mul, hG]
          simp only [Matrix.mul_assoc]
      _ = G := h2
  have s00 := congrFun (congrFun h2' 0) 0
  have s11 := congrFun (congrFun h2' 1) 1
  simp [heisC, Matrix.mul_apply, Fin.sum_univ_three] at s00 s11
  refine ⟨G 0 0, ?_⟩
  ext k l
  fin_cases k <;> fin_cases l <;> simp [g01, g02, g10, g12, g20, g21, ← s00, ← s11]

theorem exists_unitary_rescale (h : UnitaryFieldData ℓ f K) {P₀ : GL (Fin 3) K} {ν : K}
    (hν : ((P₀ : Matrix (Fin 3) (Fin 3) K).map h.bar)ᵀ * (P₀ : Matrix (Fin 3) (Fin 3) K) =
      ν • 1) :
    ∃ κ : Kˣ, GeneralLinearGroup.scalar (Fin 3) κ * P₀ ∈ primeFormUnitary h (idGram K 3) := by
  have hν00 : ν = ∑ i : Fin 3, h.bar ((P₀ : Matrix (Fin 3) (Fin 3) K) i 0) *
      (P₀ : Matrix (Fin 3) (Fin 3) K) i 0 := by
    have h00 := congrFun (congrFun hν 0) 0
    simpa [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.one_apply] using
      h00.symm
  have hbarν : h.bar ν = ν := by
    conv_lhs => rw [hν00]
    rw [map_sum]
    conv_rhs => rw [hν00]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, h.bar_bar, mul_comm]
  have hdetP₀ : (P₀ : Matrix (Fin 3) (Fin 3) K).det ≠ 0 := by
    have := (Matrix.GeneralLinearGroup.det P₀).ne_zero
    rwa [Matrix.GeneralLinearGroup.val_det_apply] at this
  have hν0 : ν ≠ 0 := by
    intro h0
    have h1 := congrArg Matrix.det hν
    have hdb : ((P₀ : Matrix (Fin 3) (Fin 3) K).map h.bar).det =
        h.bar (P₀ : Matrix (Fin 3) (Fin 3) K).det := (RingHom.map_det h.bar _).symm
    rw [h0, zero_smul, Matrix.det_mul, Matrix.det_transpose, hdb] at h1
    have h2 : (0 : Matrix (Fin 3) (Fin 3) K).det = 0 := by
      have : Nonempty (Fin 3) := ⟨0⟩
      exact Matrix.det_zero
    rw [h2] at h1
    exact mul_ne_zero ((h.bar_eq_zero_iff).not.mpr hdetP₀) hdetP₀ h1
  have hνfix : (ν⁻¹ : K) ∈ h.fixedField := by
    rw [UnitaryFieldData.mem_fixedField, map_inv₀, hbarν]
  obtain ⟨κ, hκ⟩ := h.normHom_surjective ⟨ν⁻¹, hνfix⟩
  have hκnorm : κ * h.bar κ = ν⁻¹ := by
    have := congrArg Subtype.val hκ
    simpa [UnitaryFieldData.coe_normHom, UnitaryFieldData.norm] using this
  have hκ0 : κ ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hκnorm
    exact inv_ne_zero hν0 hκnorm.symm
  refine ⟨Units.mk0 κ hκ0, ?_⟩
  rw [mem_primeFormUnitary, Units.val_mul, GeneralLinearGroup.coe_scalar, Units.val_mk0,
    Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul]
  simp only [idGram, Units.val_one]
  rw [barTranspose_smul_mul_smul, Matrix.mul_one, hν, smul_smul]
  have : h.bar κ * κ * ν = 1 := by
    rw [mul_comm (h.bar κ) κ, hκnorm]; exact inv_mul_cancel₀ hν0
  rw [this, one_smul]

theorem exists_unitary_heisenberg_basis_alpha (h : UnitaryFieldData ℓ f K)
    (hq3 : 3 ∣ ℓ ^ f + 1) {x y : GL (Fin 3) K} (hx : x ∈ primeFormUnitary h (idGram K 3))
    (hy : y ∈ primeFormUnitary h (idGram K 3)) {ω α : K} (hω : IsPrimitiveRoot ω 3)
    (hyx : (y : Matrix (Fin 3) (Fin 3) K) * x = ω • ((x : Matrix (Fin 3) (Fin 3) K) * y))
    (hy3 : (y : Matrix (Fin 3) (Fin 3) K) ^ 3 = 1)
    (hx3 : (x : Matrix (Fin 3) (Fin 3) K) ^ 3 = α • 1) :
    ∃ (P : GL (Fin 3) K) (ξ : K), P ∈ primeFormUnitary h (idGram K 3) ∧ ξ ^ 3 = 1 ∧
      (y : Matrix (Fin 3) (Fin 3) K) * P =
        P * diagonal ![ξ, ξ * ω, ξ * ω ^ 2] ∧
      (x : Matrix (Fin 3) (Fin 3) K) * P = P * heisC α := by
  obtain ⟨P₀, ξ, hξ3, hYP₀, hXP₀⟩ := exists_heisenberg_basis_gl hω hyx hy3 hx3
  have hxu := mem_primeFormUnitary.1 hx
  have hyu := mem_primeFormUnitary.1 hy
  simp only [idGram, Units.val_one, Matrix.mul_one] at hxu hyu
  obtain ⟨ν, hν⟩ := gram_eq_smul_one_alpha h hq3 hω hξ3 hxu hyu (hXP₀ : _ * _ = _ * heisC α)
    hYP₀
  obtain ⟨κ, hκ⟩ := exists_unitary_rescale h hν
  refine ⟨GeneralLinearGroup.scalar (Fin 3) κ * P₀, ξ, hκ, hξ3, ?_, ?_⟩
  · rw [Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      ← Matrix.smul_eq_diagonal_mul, Matrix.mul_smul, hYP₀, Matrix.smul_mul]
  · rw [Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      ← Matrix.smul_eq_diagonal_mul, Matrix.mul_smul, hXP₀, Matrix.smul_mul]
    rfl

end CFSG.LieType.SeitzGeneration
