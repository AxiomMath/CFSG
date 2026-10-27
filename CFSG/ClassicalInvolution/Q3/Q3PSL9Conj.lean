module

public import CFSG.ClassicalInvolution.ModelFacts.Orth15InnerL4X

public section

set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3PSL9

open Matrix
open CFSG.ClassicalInvolution.ModelFacts.Orth15.InnerL4
open scoped MatrixGroups

variable {F : Type} [Field F]

theorem eq_zero_of_sq_add_sq (hns : ¬ ∃ i : F, i * i = -1) {a b : F}
    (h : a * a + b * b = 0) : a = 0 ∧ b = 0 := by
  by_cases hb : b = 0
  · subst hb
    exact ⟨mul_self_eq_zero.mp (by simpa using h), rfl⟩
  · exact absurd ⟨a / b, by field_simp; linear_combination h⟩ hns

theorem two_ne_zero_of_not_sq (hns : ¬ ∃ i : F, i * i = -1) : (2 : F) ≠ 0 :=
  fun h => hns ⟨1, by linear_combination h⟩

section Vec

variable {U : Matrix (Fin 4) (Fin 4) F}

theorem mulVec_mulVec_of_sq_neg_one (hU : U * U = -1) (v : Fin 4 → F) :
    U *ᵥ (U *ᵥ v) = -v := by
  rw [Matrix.mulVec_mulVec, hU, Matrix.neg_mulVec, Matrix.one_mulVec]

theorem eq_zero_of_smul_add_smul_mulVec (hns : ¬ ∃ i : F, i * i = -1) (hU : U * U = -1)
    {v : Fin 4 → F} (hv : v ≠ 0) {a b : F} (h : a • v + b • (U *ᵥ v) = 0) :
    a = 0 ∧ b = 0 := by
  have h1 : (a * a + b * b) • v = 0 := by
    have h2 : a • (a • v + b • (U *ᵥ v)) - b • (U *ᵥ (a • v + b • (U *ᵥ v))) = 0 := by
      rw [h, Matrix.mulVec_zero, smul_zero, smul_zero, sub_zero]
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
      mulVec_mulVec_of_sq_neg_one hU] at h2
    rw [← h2]
    module
  rcases smul_eq_zero.mp h1 with h3 | h3
  · exact eq_zero_of_sq_add_sq hns h3
  · exact absurd h3 hv

theorem exists_not_mem_span [Finite F] (v w : Fin 4 → F) :
    ∃ x : Fin 4 → F, ∀ α β : F, x ≠ α • v + β • w := by
  by_contra h
  push Not at h
  have hs : Function.Surjective (fun p : F × F => p.1 • v + p.2 • w) := fun x => by
    obtain ⟨α, β, hx⟩ := h x
    exact ⟨(α, β), hx.symm⟩
  have h1 := Nat.card_le_card_of_surjective _ hs
  have : Fintype F := Fintype.ofFinite F
  rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin 4 → F), Fintype.card_fun,
    Fintype.card_fin, ← Nat.card_eq_fintype_card, ← sq] at h1
  have h2 : 1 < Nat.card F := Finite.one_lt_card
  have h3 := Nat.pow_lt_pow_right h2 (show 2 < 4 by norm_num)
  omega

@[expose] def basisMat (U : Matrix (Fin 4) (Fin 4) F) (v₁ v₂ : Fin 4 → F) :
    Matrix (Fin 4) (Fin 4) F :=
  Matrix.of fun i j => ![v₁ i, -(U *ᵥ v₁) i, v₂ i, -(U *ᵥ v₂) i] j

theorem basisMat_mulVec (v₁ v₂ x : Fin 4 → F) :
    basisMat U v₁ v₂ *ᵥ x =
      x 0 • v₁ + (-x 1) • (U *ᵥ v₁) + x 2 • v₂ + (-x 3) • (U *ᵥ v₂) := by
  ext i
  simp [basisMat, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
  ring

theorem independent_of_basis (hns : ¬ ∃ i : F, i * i = -1) (hU : U * U = -1) {v₁ v₂ : Fin 4 → F}
    (h₁ : v₁ ≠ 0) (h₂ : ∀ α β : F, v₂ ≠ α • v₁ + β • (U *ᵥ v₁)) (a b c d : F)
    (hvec : a • v₁ + b • (U *ᵥ v₁) + c • v₂ + d • (U *ᵥ v₂) = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 := by
  have hcd : c * c + d * d = 0 := by
    by_contra hne
    have h3 : c • (a • v₁ + b • (U *ᵥ v₁) + c • v₂ + d • (U *ᵥ v₂)) -
        d • (U *ᵥ (a • v₁ + b • (U *ᵥ v₁) + c • v₂ + d • (U *ᵥ v₂))) = 0 := by
      rw [hvec, Matrix.mulVec_zero, smul_zero, smul_zero, sub_zero]
    rw [Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul,
      Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_smul,
      mulVec_mulVec_of_sq_neg_one hU, mulVec_mulVec_of_sq_neg_one hU] at h3
    have h4 : (c * c + d * d) • v₂ =
        (-(c * a + d * b)) • v₁ + (-(c * b - d * a)) • (U *ᵥ v₁) := by
      linear_combination (norm := module) h3
    refine h₂ (-(c * a + d * b) / (c * c + d * d)) (-(c * b - d * a) / (c * c + d * d)) ?_
    calc v₂ = (c * c + d * d)⁻¹ • ((c * c + d * d) • v₂) := (inv_smul_smul₀ hne v₂).symm
      _ = _ := by
        rw [h4]
        module
  obtain ⟨hc, hd⟩ := eq_zero_of_sq_add_sq hns hcd
  subst hc
  subst hd
  have h5 : a • v₁ + b • (U *ᵥ v₁) = 0 := by simpa using hvec
  obtain ⟨ha, hb⟩ := eq_zero_of_smul_add_smul_mulVec hns hU h₁ h5
  exact ⟨ha, hb, rfl, rfl⟩

theorem det_basisMat_ne_zero (hns : ¬ ∃ i : F, i * i = -1) (hU : U * U = -1) {v₁ v₂ : Fin 4 → F}
    (h₁ : v₁ ≠ 0) (h₂ : ∀ α β : F, v₂ ≠ α • v₁ + β • (U *ᵥ v₁)) :
    (basisMat U v₁ v₂).det ≠ 0 := by
  intro hdet
  obtain ⟨x, hx, hPx⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  rw [basisMat_mulVec] at hPx
  obtain ⟨ha, hb, hc, hd⟩ := independent_of_basis hns hU h₁ h₂ (x 0) (-x 1) (x 2) (-x 3) hPx
  apply hx
  ext i
  fin_cases i
  · simpa using ha
  · simpa using hb
  · simpa using hc
  · simpa using hd

end Vec

theorem mul_basisMat_eq {U : Matrix (Fin 4) (Fin 4) F} (hU : U * U = -1) (v₁ v₂ : Fin 4 → F) :
    U * basisMat U v₁ v₂ =
      basisMat U v₁ v₂ * !![0, 1, 0, 0; -1, 0, 0, 0; 0, 0, 0, 1; 0, 0, -1, 0] := by
  refine Matrix.ext_of_mulVec_single fun j => ?_
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  have hP : ∀ k, basisMat U v₁ v₂ *ᵥ Pi.single k 1 = fun i => basisMat U v₁ v₂ i k := fun k =>
    Matrix.mulVec_single_one _ _
  have hJ : ∀ k, (!![0, 1, 0, 0; -1, 0, 0, 0; 0, 0, 0, 1; 0, 0, -1, 0] : Matrix (Fin 4) (Fin 4) F)
      *ᵥ Pi.single k 1 = fun i => (!![0, 1, 0, 0; -1, 0, 0, 0; 0, 0, 0, 1; 0, 0, -1, 0] :
        Matrix (Fin 4) (Fin 4) F) i k := fun k => Matrix.mulVec_single_one _ _
  have hP0 : basisMat U v₁ v₂ *ᵥ Pi.single 0 1 = v₁ := by
    rw [hP]; ext i; simp [basisMat]
  have hP1 : basisMat U v₁ v₂ *ᵥ Pi.single 1 1 = -(U *ᵥ v₁) := by
    rw [hP]; ext i; simp [basisMat]
  have hP2 : basisMat U v₁ v₂ *ᵥ Pi.single 2 1 = v₂ := by
    rw [hP]; ext i; simp [basisMat]
  have hP3 : basisMat U v₁ v₂ *ᵥ Pi.single 3 1 = -(U *ᵥ v₂) := by
    rw [hP]; ext i; simp [basisMat]
  have hJ0 : (!![0, 1, 0, 0; -1, 0, 0, 0; 0, 0, 0, 1; 0, 0, -1, 0] : Matrix (Fin 4) (Fin 4) F)
      *ᵥ Pi.single 0 1 = -(Pi.single 1 1) := by
    rw [hJ]; ext i; fin_cases i <;> simp
  have hJ1 : (!![0, 1, 0, 0; -1, 0, 0, 0; 0, 0, 0, 1; 0, 0, -1, 0] : Matrix (Fin 4) (Fin 4) F)
      *ᵥ Pi.single 1 1 = Pi.single 0 1 := by
    rw [hJ]; ext i; fin_cases i <;> simp
  have hJ2 : (!![0, 1, 0, 0; -1, 0, 0, 0; 0, 0, 0, 1; 0, 0, -1, 0] : Matrix (Fin 4) (Fin 4) F)
      *ᵥ Pi.single 2 1 = -(Pi.single 3 1) := by
    rw [hJ]; ext i; fin_cases i <;> simp
  have hJ3 : (!![0, 1, 0, 0; -1, 0, 0, 0; 0, 0, 0, 1; 0, 0, -1, 0] : Matrix (Fin 4) (Fin 4) F)
      *ᵥ Pi.single 3 1 = Pi.single 2 1 := by
    rw [hJ]; ext i; fin_cases i <;> simp
  fin_cases j
  · simp only [Fin.zero_eta, hP0, hJ0, Matrix.mulVec_neg, hP1, neg_neg]
  · simp only [Fin.mk_one, hP1, hJ1, hP0, Matrix.mulVec_neg, mulVec_mulVec_of_sq_neg_one hU,
      neg_neg]
  · simp only [Fin.reduceFinMk, Fin.isValue, hP2, hJ2, Matrix.mulVec_neg, hP3, neg_neg]
  · simp only [Fin.reduceFinMk, Fin.isValue, hP3, hJ3, hP2, Matrix.mulVec_neg,
      mulVec_mulVec_of_sq_neg_one hU, neg_neg]

theorem exists_conj_u0_sl4 [Finite F] (hns : ¬ ∃ i : F, i * i = -1) (u : SL(4, F))
    (hu : u * u = zneg F) : ∃ g : SL(4, F), g * u0 F * g⁻¹ = u := by
  have hU : (u : Matrix (Fin 4) (Fin 4) F) * u = -1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, hu, coe_zneg]
  have h2 := two_ne_zero_of_not_sq hns
  obtain ⟨v₁, hv₁⟩ : ∃ v : Fin 4 → F, v ≠ 0 :=
    ⟨Pi.single 0 1, fun h => by simpa using congrFun h 0⟩
  obtain ⟨v₂, hv₂⟩ := exists_not_mem_span v₁ ((u : Matrix (Fin 4) (Fin 4) F) *ᵥ v₁)
  set U : Matrix (Fin 4) (Fin 4) F := (u : Matrix (Fin 4) (Fin 4) F) with hUdef
  set P : Matrix (Fin 4) (Fin 4) F := basisMat U v₁ v₂ with hP
  set J : Matrix (Fin 4) (Fin 4) F :=
    !![0, 1, 0, 0; -1, 0, 0, 0; 0, 0, 0, 1; 0, 0, -1, 0] with hJ
  have hPdet : P.det ≠ 0 := det_basisMat_ne_zero hns hU hv₁ hv₂
  have hUP : U * P = P * J := mul_basisMat_eq hU v₁ v₂
  obtain ⟨x, y, hxy⟩ := exists_sq_add_sq h2 (P.det)⁻¹
  set S : Matrix (Fin 4) (Fin 4) F := !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, x, -y; 0, 0, y, x] with hS
  have hSdet : S.det = x * x + y * y := by
    rw [hS, Matrix.det_succ_row_zero]
    simp [Fin.sum_univ_succ, Fin.succAbove, Matrix.det_succ_row_zero]
  have hJS : J * S = S * J := by
    rw [hJ, hS]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]
  have hgdet : (P * S).det = 1 := by
    rw [Matrix.det_mul, hSdet, hxy, mul_inv_cancel₀ hPdet]
  let g : SL(4, F) := ⟨P * S, hgdet⟩
  refine ⟨g, ?_⟩
  rw [mul_inv_eq_iff_eq_mul]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_u0]
  change P * S * J = U * (P * S)
  calc P * S * J = P * (S * J) := Matrix.mul_assoc _ _ _
    _ = P * (J * S) := by rw [hJS]
    _ = P * J * S := (Matrix.mul_assoc _ _ _).symm
    _ = U * P * S := by rw [hUP]
    _ = U * (P * S) := Matrix.mul_assoc _ _ _

end CFSG.ClassicalInvolution.Q3.Q3PSL9
