module

public import CFSG.LocalAnalysis.ComponentClassification.OddSelectorSplitFour

public noncomputable section

namespace CFSG.ComponentClassification.OddSelector

namespace Catalog7L4E

open Matrix

variable {k : Type*} [Field k]

@[expose] def detPolar (X Y : Matrix (Fin 2) (Fin 2) k) : k := (X + Y).det - X.det - Y.det

theorem detPolar_eq (X Y : Matrix (Fin 2) (Fin 2) k) :
    detPolar X Y = X 0 0 * Y 1 1 + Y 0 0 * X 1 1 - X 0 1 * Y 1 0 - Y 0 1 * X 1 0 := by
  simp only [detPolar, det_fin_two, Matrix.add_apply]
  ring

theorem detPolar_add_right (X Y Y' : Matrix (Fin 2) (Fin 2) k) :
    detPolar X (Y + Y') = detPolar X Y + detPolar X Y' := by
  simp only [detPolar_eq, Matrix.add_apply]
  ring

theorem detPolar_neg_right (X Y : Matrix (Fin 2) (Fin 2) k) :
    detPolar X (-Y) = -detPolar X Y := by
  simp only [detPolar_eq, Matrix.neg_apply]
  ring

theorem detPolar_mul_right (X N Y : Matrix (Fin 2) (Fin 2) k) :
    detPolar (X * N) Y = detPolar X (Y * adjugate N) := by
  simp only [detPolar_eq, mul_apply, adjugate_fin_two, Fin.sum_univ_two, of_apply, cons_val',
    cons_val_zero, cons_val_one, empty_val', cons_val_fin_one]
  ring

theorem detPolar_mul_left (N X Y : Matrix (Fin 2) (Fin 2) k) :
    detPolar (N * X) Y = detPolar X (adjugate N * Y) := by
  simp only [detPolar_eq, mul_apply, adjugate_fin_two, Fin.sum_univ_two, of_apply, cons_val',
    cons_val_zero, cons_val_one, empty_val', cons_val_fin_one]
  ring

theorem eq_zero_of_detPolar {Z : Matrix (Fin 2) (Fin 2) k}
    (h : ∀ X : Matrix (Fin 2) (Fin 2) k, detPolar X Z = 0) : Z = 0 := by
  have h1 := h !![1, 0; 0, 0]
  have h2 := h !![0, 0; 0, 1]
  have h3 := h !![0, 1; 0, 0]
  have h4 := h !![0, 0; 1, 0]
  simp [detPolar_eq] at h1 h2 h3 h4
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h1, h2, h3, h4]

theorem eq_scalar_of_adjugate_eq (h2 : (2 : k) ≠ 0) {N : Matrix (Fin 2) (Fin 2) k}
    (h : adjugate N = N) : N = (N 0 0) • (1 : Matrix (Fin 2) (Fin 2) k) := by
  rw [adjugate_fin_two] at h
  have h00 := congrFun (congrFun h 0) 0
  have h01 := congrFun (congrFun h 0) 1
  have h10 := congrFun (congrFun h 1) 0
  simp at h00 h01 h10
  have h01' : N 0 1 = 0 := by
    have : (2 : k) * N 0 1 = 0 := by linear_combination -h01
    exact (mul_eq_zero.mp this).resolve_left h2
  have h10' : N 1 0 = 0 := by
    have : (2 : k) * N 1 0 = 0 := by linear_combination -h10
    exact (mul_eq_zero.mp this).resolve_left h2
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h01', h10', h00]

@[expose] def unipUpper (k : Type*) [Field k] : SpecialLinearGroup (Fin 2) k :=
  ⟨!![1, 1; 0, 1], by rw [det_fin_two_of]; ring⟩

@[expose] def unipLower (k : Type*) [Field k] : SpecialLinearGroup (Fin 2) k :=
  ⟨!![1, 0; 1, 1], by rw [det_fin_two_of]; ring⟩

@[expose] def diagUnit {a : k} (ha : a ≠ 0) : SpecialLinearGroup (Fin 2) k :=
  ⟨!![a, 0; 0, a⁻¹], by rw [det_fin_two_of]; field_simp; ring⟩

theorem eq_mul_of_commute_left {a : k} (ha : a ≠ 0) (ha1 : a ^ 2 ≠ 1)
    (w : Matrix (Fin 2) (Fin 2) k →ₗ[k] Matrix (Fin 2) (Fin 2) k)
    (hw : ∀ (U : SpecialLinearGroup (Fin 2) k) (X : Matrix (Fin 2) (Fin 2) k),
      w ((U : Matrix (Fin 2) (Fin 2) k) * X) = (U : Matrix (Fin 2) (Fin 2) k) * w X)
    (X : Matrix (Fin 2) (Fin 2) k) : w X = X * w 1 := by
  have hsub : ∀ Y : Matrix (Fin 2) (Fin 2) k,
      (∀ Z, w (Y * Z) = Y * w Z) → ∀ Y' : Matrix (Fin 2) (Fin 2) k,
      (∀ Z, w (Y' * Z) = Y' * w Z) → ∀ c c' : k, ∀ Z,
        w ((c • Y + c' • Y') * Z) = (c • Y + c' • Y') * w Z := by
    intro Y hY Y' hY' c c' Z
    rw [Matrix.add_mul, map_add, Matrix.smul_mul, Matrix.smul_mul, map_smul, map_smul, hY, hY',
      Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul]
  have h1 : ∀ Z, w ((1 : Matrix (Fin 2) (Fin 2) k) * Z) = 1 * w Z := fun Z => by
    rw [Matrix.one_mul, Matrix.one_mul]
  have hu : ∀ Z, w ((unipUpper k : Matrix (Fin 2) (Fin 2) k) * Z) =
      (unipUpper k : Matrix (Fin 2) (Fin 2) k) * w Z := hw _
  have hl : ∀ Z, w ((unipLower k : Matrix (Fin 2) (Fin 2) k) * Z) =
      (unipLower k : Matrix (Fin 2) (Fin 2) k) * w Z := hw _
  have hd : ∀ Z, w ((diagUnit ha : Matrix (Fin 2) (Fin 2) k) * Z) =
      (diagUnit ha : Matrix (Fin 2) (Fin 2) k) * w Z := hw _
  have hne : a - a⁻¹ ≠ 0 := by
    intro h
    apply ha1
    have : a = a⁻¹ := sub_eq_zero.mp h
    calc a ^ 2 = a * a⁻¹ := by rw [sq, ← this]
      _ = 1 := mul_inv_cancel₀ ha
  have e12 : (1 : k) • (unipUpper k : Matrix (Fin 2) (Fin 2) k) + (-1 : k) • 1 =
      !![0, 1; 0, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [unipUpper]
  have e21 : (1 : k) • (unipLower k : Matrix (Fin 2) (Fin 2) k) + (-1 : k) • 1 =
      !![0, 0; 1, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [unipLower]
  have e11 : (a - a⁻¹)⁻¹ • (diagUnit ha : Matrix (Fin 2) (Fin 2) k) +
      (-(a - a⁻¹)⁻¹ * a⁻¹) • 1 = !![1, 0; 0, 0] := by
    ext i j
    fin_cases i <;> fin_cases j
    · simp [diagUnit]
      field_simp
      ring
    · simp [diagUnit]
    · simp [diagUnit]
    · simp [diagUnit]
  have e22 : (1 : k) • (1 : Matrix (Fin 2) (Fin 2) k) + (-1 : k) • !![1, 0; 0, 0] =
      !![0, 0; 0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have h12 := hsub _ hu _ h1 1 (-1)
  rw [e12] at h12
  have h21 := hsub _ hl _ h1 1 (-1)
  rw [e21] at h21
  have h11 := hsub _ hd _ h1 (a - a⁻¹)⁻¹ (-(a - a⁻¹)⁻¹ * a⁻¹)
  rw [e11] at h11
  have h22 := hsub _ h1 _ h11 1 (-1)
  rw [e22] at h22
  have hall : ∀ Y Z : Matrix (Fin 2) (Fin 2) k, w (Y * Z) = Y * w Z := by
    intro Y Z
    have hY : Y = (Y 0 0 • !![1, 0; 0, 0] + Y 0 1 • !![0, 1; 0, 0]) +
        (Y 1 0 • !![0, 0; 1, 0] + Y 1 1 • !![0, 0; 0, 1]) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    have hA := hsub _ h11 _ h12 (Y 0 0) (Y 0 1)
    have hB := hsub _ h21 _ h22 (Y 1 0) (Y 1 1)
    have hC := hsub _ hA _ hB 1 1
    simp only [one_smul] at hC
    rw [hY]
    exact hC Z
  calc w X = w (X * 1) := by rw [Matrix.mul_one]
    _ = X * w 1 := hall X 1

theorem eq_mul_of_commute_right {a : k} (ha : a ≠ 0) (ha1 : a ^ 2 ≠ 1)
    (w : Matrix (Fin 2) (Fin 2) k →ₗ[k] Matrix (Fin 2) (Fin 2) k)
    (hw : ∀ (U : SpecialLinearGroup (Fin 2) k) (X : Matrix (Fin 2) (Fin 2) k),
      w (X * (U : Matrix (Fin 2) (Fin 2) k)) = w X * (U : Matrix (Fin 2) (Fin 2) k))
    (X : Matrix (Fin 2) (Fin 2) k) : w X = w 1 * X := by
  let τ : Matrix (Fin 2) (Fin 2) k ≃ₗ[k] Matrix (Fin 2) (Fin 2) k :=
    { toFun := fun Y => Yᵀ
      invFun := fun Y => Yᵀ
      map_add' := fun Y Z => transpose_add Y Z
      map_smul' := fun c Y => transpose_smul c Y
      left_inv := fun Y => transpose_transpose Y
      right_inv := fun Y => transpose_transpose Y }
  let w' : Matrix (Fin 2) (Fin 2) k →ₗ[k] Matrix (Fin 2) (Fin 2) k :=
    (τ : Matrix (Fin 2) (Fin 2) k →ₗ[k] _).comp (w.comp (τ : Matrix (Fin 2) (Fin 2) k →ₗ[k] _))
  have hw' : ∀ (U : SpecialLinearGroup (Fin 2) k) (Y : Matrix (Fin 2) (Fin 2) k),
      w' ((U : Matrix (Fin 2) (Fin 2) k) * Y) = (U : Matrix (Fin 2) (Fin 2) k) * w' Y := by
    intro U Y
    have hUt : ((U : Matrix (Fin 2) (Fin 2) k))ᵀ.det = 1 := by rw [det_transpose, U.2]
    have h := hw ⟨(U : Matrix (Fin 2) (Fin 2) k)ᵀ, hUt⟩ Yᵀ
    change (w ((U * Y : Matrix (Fin 2) (Fin 2) k))ᵀ)ᵀ = U * (w Yᵀ)ᵀ
    rw [transpose_mul]
    change w (Yᵀ * (U : Matrix (Fin 2) (Fin 2) k)ᵀ) = w Yᵀ * (U : Matrix (Fin 2) (Fin 2) k)ᵀ
      at h
    rw [h, transpose_mul, transpose_transpose]
  have h1 := eq_mul_of_commute_left ha ha1 w' hw' Xᵀ
  change (w Xᵀᵀ)ᵀ = Xᵀ * (w 1ᵀ)ᵀ at h1
  rw [transpose_transpose, transpose_one] at h1
  have h2 := congrArg transpose h1
  rwa [transpose_transpose, transpose_mul, transpose_transpose, transpose_transpose] at h2

variable (ψ : (Fin 4 → k) ≃ₗ[k] Matrix (Fin 2) (Fin 2) k)

theorem two_mul_dotProduct_eq {R : Matrix (Fin 4) (Fin 4) k} (hR : Rᵀ = R)
    (hQ : ∀ v, v ⬝ᵥ (R *ᵥ v) = (ψ v).det) (u v : Fin 4 → k) :
    2 * (u ⬝ᵥ (R *ᵥ v)) = detPolar (ψ u) (ψ v) := by
  have hsym : v ⬝ᵥ (R *ᵥ u) = u ⬝ᵥ (R *ᵥ v) := by
    rw [dotProduct_mulVec, dotProduct_comm, ← mulVec_transpose, hR]
  have h := hQ (u + v)
  rw [map_add, mulVec_add, dotProduct_add, add_dotProduct, add_dotProduct, hQ u, hQ v,
    hsym] at h
  rw [detPolar, ← h]
  ring

theorem dotProduct_selfAdjoint {R W : Matrix (Fin 4) (Fin 4) k} (hsa : Wᵀ * R = R * W)
    (u v : Fin 4 → k) : (W *ᵥ u) ⬝ᵥ (R *ᵥ v) = u ⬝ᵥ (R *ᵥ (W *ᵥ v)) := by
  rw [← vecMul_transpose, ← dotProduct_mulVec, mulVec_mulVec, hsa, ← mulVec_mulVec]

theorem eq_scalar_of_mulVec {W : GL (Fin 4) k} {c : k}
    (h : ∀ v, (W : Matrix (Fin 4) (Fin 4) k) *ᵥ v = c • v) :
    ∃ c' : kˣ, W = GeneralLinearGroup.scalar (Fin 4) c' := by
  have hc : c ≠ 0 := by
    intro hc
    have h1 := h (((W⁻¹ : GL (Fin 4) k) : Matrix (Fin 4) (Fin 4) k) *ᵥ
      (Pi.single 0 1 : Fin 4 → k))
    rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec, hc,
      zero_smul] at h1
    have := congrFun h1 0
    simp at this
  refine ⟨Units.mk0 c hc, eq_of_mulVec_eq fun v => ?_⟩
  rw [h, GeneralLinearGroup.coe_scalar, Units.val_mk0]
  ext i
  simp [scalar_apply, mulVec_diagonal]

theorem eq_scalar_of_commute_splitLeft (h2 : (2 : k) ≠ 0) {a : k} (ha : a ≠ 0) (ha1 : a ^ 2 ≠ 1)
    {R : Matrix (Fin 4) (Fin 4) k} (hR : Rᵀ = R) (hQ : ∀ v, v ⬝ᵥ (R *ᵥ v) = (ψ v).det)
    (W : GL (Fin 4) k) (hW : ∀ U, W * splitLeftHom ψ U = splitLeftHom ψ U * W)
    (hsa : (W : Matrix (Fin 4) (Fin 4) k)ᵀ * R = R * W) :
    ∃ c : kˣ, W = GeneralLinearGroup.scalar (Fin 4) c := by
  let w : Matrix (Fin 2) (Fin 2) k →ₗ[k] Matrix (Fin 2) (Fin 2) k :=
    (ψ : (Fin 4 → k) →ₗ[k] Matrix (Fin 2) (Fin 2) k).comp
      ((Matrix.toLin' (W : Matrix (Fin 4) (Fin 4) k)).comp
        (ψ.symm : Matrix (Fin 2) (Fin 2) k →ₗ[k] (Fin 4 → k)))
  have hw : ∀ X, w X = ψ ((W : Matrix (Fin 4) (Fin 4) k) *ᵥ ψ.symm X) := fun X => rfl
  have hwU : ∀ (U : SpecialLinearGroup (Fin 2) k) (X : Matrix (Fin 2) (Fin 2) k),
      w ((U : Matrix (Fin 2) (Fin 2) k) * X) = (U : Matrix (Fin 2) (Fin 2) k) * w X := by
    intro U X
    have h1 : ψ.symm ((U : Matrix (Fin 2) (Fin 2) k) * X) =
        ((splitLeftHom ψ U : GL (Fin 4) k) : Matrix (Fin 4) (Fin 4) k) *ᵥ ψ.symm X := by
      rw [splitLeftHom_mulVec, LinearEquiv.apply_symm_apply]
    rw [hw, hw, h1, mulVec_mulVec, ← Units.val_mul, hW U, Units.val_mul, ← mulVec_mulVec,
      splitLeftHom_mulVec, LinearEquiv.apply_symm_apply]
  have hwN := eq_mul_of_commute_left ha ha1 w hwU
  set N := w 1 with hNdef
  have hβ : ∀ X Y : Matrix (Fin 2) (Fin 2) k, detPolar (X * N) Y = detPolar X (Y * N) := by
    intro X Y
    have e1 := two_mul_dotProduct_eq ψ hR hQ ((W : Matrix (Fin 4) (Fin 4) k) *ᵥ ψ.symm X)
      (ψ.symm Y)
    have e2 := two_mul_dotProduct_eq ψ hR hQ (ψ.symm X)
      ((W : Matrix (Fin 4) (Fin 4) k) *ᵥ ψ.symm Y)
    rw [dotProduct_selfAdjoint hsa, e2] at e1
    rw [← hwN, ← hwN, hw, hw]
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at e1
    exact e1.symm
  have hadj : adjugate N = N := by
    have h1 : ∀ Y : Matrix (Fin 2) (Fin 2) k, Y * adjugate N + -(Y * N) = 0 := by
      intro Y
      apply eq_zero_of_detPolar
      intro X
      rw [detPolar_add_right, detPolar_neg_right, ← detPolar_mul_right, hβ, add_neg_cancel]
    have := h1 1
    rw [Matrix.one_mul, Matrix.one_mul] at this
    exact neg_add_eq_zero.mp (by rw [add_comm]; exact this) |>.symm
  have hNs := eq_scalar_of_adjugate_eq h2 hadj
  refine eq_scalar_of_mulVec (c := N 0 0) fun v => ?_
  have h1 : ψ ((W : Matrix (Fin 4) (Fin 4) k) *ᵥ v) = ψ v * N := by
    have := hwN (ψ v)
    rwa [hw, LinearEquiv.symm_apply_apply] at this
  rw [hNs, Matrix.mul_smul, Matrix.mul_one, ← map_smul] at h1
  exact ψ.injective h1

theorem eq_scalar_of_commute_splitRight (h2 : (2 : k) ≠ 0) {a : k} (ha : a ≠ 0)
    (ha1 : a ^ 2 ≠ 1) {R : Matrix (Fin 4) (Fin 4) k} (hR : Rᵀ = R)
    (hQ : ∀ v, v ⬝ᵥ (R *ᵥ v) = (ψ v).det)
    (W : GL (Fin 4) k) (hW : ∀ U, W * splitRightHom ψ U = splitRightHom ψ U * W)
    (hsa : (W : Matrix (Fin 4) (Fin 4) k)ᵀ * R = R * W) :
    ∃ c : kˣ, W = GeneralLinearGroup.scalar (Fin 4) c := by
  let w : Matrix (Fin 2) (Fin 2) k →ₗ[k] Matrix (Fin 2) (Fin 2) k :=
    (ψ : (Fin 4 → k) →ₗ[k] Matrix (Fin 2) (Fin 2) k).comp
      ((Matrix.toLin' (W : Matrix (Fin 4) (Fin 4) k)).comp
        (ψ.symm : Matrix (Fin 2) (Fin 2) k →ₗ[k] (Fin 4 → k)))
  have hw : ∀ X, w X = ψ ((W : Matrix (Fin 4) (Fin 4) k) *ᵥ ψ.symm X) := fun X => rfl
  have hwU : ∀ (U : SpecialLinearGroup (Fin 2) k) (X : Matrix (Fin 2) (Fin 2) k),
      w (X * (U : Matrix (Fin 2) (Fin 2) k)) = w X * (U : Matrix (Fin 2) (Fin 2) k) := by
    intro U X
    have h1 : ψ.symm (X * (U : Matrix (Fin 2) (Fin 2) k)) =
        ((splitRightHom ψ U⁻¹ : GL (Fin 4) k) : Matrix (Fin 4) (Fin 4) k) *ᵥ ψ.symm X := by
      rw [splitRightHom_mulVec, LinearEquiv.apply_symm_apply, inv_inv]
    rw [hw, hw, h1, mulVec_mulVec, ← Units.val_mul, hW, Units.val_mul, ← mulVec_mulVec,
      splitRightHom_mulVec, LinearEquiv.apply_symm_apply, inv_inv]
  have hwN := eq_mul_of_commute_right ha ha1 w hwU
  set N := w 1 with hNdef
  have hβ : ∀ X Y : Matrix (Fin 2) (Fin 2) k, detPolar (N * X) Y = detPolar X (N * Y) := by
    intro X Y
    have e1 := two_mul_dotProduct_eq ψ hR hQ ((W : Matrix (Fin 4) (Fin 4) k) *ᵥ ψ.symm X)
      (ψ.symm Y)
    have e2 := two_mul_dotProduct_eq ψ hR hQ (ψ.symm X)
      ((W : Matrix (Fin 4) (Fin 4) k) *ᵥ ψ.symm Y)
    rw [dotProduct_selfAdjoint hsa, e2] at e1
    rw [← hwN, ← hwN, hw, hw]
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at e1
    exact e1.symm
  have hadj : adjugate N = N := by
    have h1 : ∀ Y : Matrix (Fin 2) (Fin 2) k, adjugate N * Y + -(N * Y) = 0 := by
      intro Y
      apply eq_zero_of_detPolar
      intro X
      rw [detPolar_add_right, detPolar_neg_right, ← detPolar_mul_left, hβ, add_neg_cancel]
    have := h1 1
    rw [Matrix.mul_one, Matrix.mul_one] at this
    exact neg_add_eq_zero.mp (by rw [add_comm]; exact this) |>.symm
  have hNs := eq_scalar_of_adjugate_eq h2 hadj
  refine eq_scalar_of_mulVec (c := N 0 0) fun v => ?_
  have h1 : ψ ((W : Matrix (Fin 4) (Fin 4) k) *ᵥ v) = N * ψ v := by
    have := hwN (ψ v)
    rwa [hw, LinearEquiv.symm_apply_apply] at this
  rw [hNs, Matrix.smul_mul, Matrix.one_mul, ← map_smul] at h1
  exact ψ.injective h1

end Catalog7L4E

end CFSG.ComponentClassification.OddSelector
