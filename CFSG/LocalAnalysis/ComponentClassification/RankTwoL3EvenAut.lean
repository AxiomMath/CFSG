module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoL3EvenMatrix
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneCoprimeCentral
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSLInnerInvolution
public import CFSG.RankThree.SteinbergR3ELinearFieldDescent
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoHypIIL3Rigid
import CFSG.LocalAnalysis.ComponentInitial.LinearHigherConjAutInner

public noncomputable section

namespace CFSG.ComponentClassification.RankTwoL3Even

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial LinearFlag FieldFourCover ProjectivePlane
open CFSG.LieType.Chevalley
open scoped commutatorElement

variable {F : Type} [Field F]

theorem three_eq_one_of_charTwo [CharP F 2] : (3 : F) = 1 := by
  have h : (2 : F) = 0 := CharTwo.two_eq_zero
  linear_combination h

theorem mul_eq_mul_of_conjAut_proj_eq {A : GL (Fin 3) F} {g h : SpecialLinearGroup (Fin 3) F}
    (htr : trace (g : Matrix (Fin 3) (Fin 3) F) = trace (h : Matrix (Fin 3) (Fin 3) F))
    (h0 : trace (h : Matrix (Fin 3) (Fin 3) F) ≠ 0)
    (heq : conjAut 3 F A (proj 3 F g) = proj 3 F h) :
    (A : Matrix (Fin 3) (Fin 3) F) * g = h * A := by
  rw [conjAut_proj] at heq
  obtain ⟨ω, -, hω⟩ := eq_mul_scalar_of_proj_eq heq
  rw [coe_slConjugation] at hω
  have htr' : trace (h : Matrix (Fin 3) (Fin 3) F) = ω * trace (h : Matrix (Fin 3) (Fin 3) F) := by
    conv_lhs => rw [hω]
    rw [trace_mul_scalar, Matrix.trace_mul_cycle, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      one_mul, htr]
  have hω1 : (ω : F) = 1 := by
    have : (1 - (ω : F)) * trace (h : Matrix (Fin 3) (Fin 3) F) = 0 := by
      linear_combination htr'
    exact (sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right h0)).symm
  rw [hω, hω1, map_one, mul_one, mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    mul_one]

theorem trace_projLevi_vSL (c : F) :
    trace (levi13 F (vSL c) : Matrix (Fin 3) (Fin 3) F) = 3 := by
  rw [coe_levi13]
  simp [trace_fin_three, vSL]
  norm_num

theorem mul_unipU_center_apply (M : Matrix (Fin 3) (Fin 3) F) (s : F) (i j : Fin 3) :
    (M * (unipU F 0 0 s : Matrix (Fin 3) (Fin 3) F)) i j =
      M i j + if j = 2 then s * M i 0 else 0 := by
  rw [coe_unipU]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, mul_comm, add_comm]

theorem unipU_center_mul_apply (M : Matrix (Fin 3) (Fin 3) F) (s : F) (i j : Fin 3) :
    ((unipU F 0 0 s : Matrix (Fin 3) (Fin 3) F) * M) i j =
      M i j + if i = 0 then s * M 2 j else 0 := by
  rw [coe_unipU]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem mul_levi13_vSL_apply (M : Matrix (Fin 3) (Fin 3) F) (s : F) (i j : Fin 3) :
    (M * (levi13 F (vSL s) : Matrix (Fin 3) (Fin 3) F)) i j =
      M i j + if j = 0 then s * M i 2 else 0 := by
  rw [coe_levi13]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, vSL, mul_comm]

theorem levi13_vSL_mul_apply (M : Matrix (Fin 3) (Fin 3) F) (s : F) (i j : Fin 3) :
    ((levi13 F (vSL s) : Matrix (Fin 3) (Fin 3) F) * M) i j =
      M i j + if i = 2 then s * M 0 j else 0 := by
  rw [coe_levi13]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, vSL, add_comm]

theorem fieldAut_proj_unipU (σ : F ≃+* F) (a b c : F) :
    fieldAut 3 F σ (proj 3 F (unipU F a b c)) = proj 3 F (unipU F (σ a) (σ b) (σ c)) := by
  rw [fieldAut_proj]
  congr 1
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, coe_unipU, coe_unipU]
  fin_cases i <;> fin_cases j <;> simp

theorem fieldAut_projLevi_vSL (σ : F ≃+* F) (c : F) :
    fieldAut 3 F σ (projLevi F (vSL c)) = projLevi F (vSL (σ c)) := by
  rw [projLevi_apply, projLevi_apply, fieldAut_proj]
  congr 1
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, coe_levi13, coe_levi13]
  fin_cases i <;> fin_cases j <;> simp [vSL]

theorem dualAut_proj_unipU_center [CharP F 2] (c : F) :
    dualAut 3 F (proj 3 F (unipU F 0 0 c)) = projLevi F (vSL c) := by
  rw [dualAut_proj, projLevi_apply, unipU_inv]
  congr 1
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  rw [Matrix.SpecialLinearGroup.coe_transpose, coe_unipU, coe_levi13]
  fin_cases i <;> fin_cases j <;> simp [vSL, CharTwo.neg_eq]

theorem proj_unipU_center_eq_projLevi (c : F) :
    proj 3 F (unipU F 0 0 c) = projLevi F (uSL c) := by
  rw [projLevi_apply, unipU_zero_zero_eq_levi13]

theorem torusGL_pow (b : Fˣ) (n : ℕ) : torusGL b ^ n = torusGL (b ^ n) := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, coe_torusGL, coe_torusGL, diagonal_pow]
  congr 1
  funext i
  fin_cases i <;> simp

theorem torusGL_one : torusGL (1 : Fˣ) = 1 := by
  apply Units.ext
  show diagonal ![1, ((1 : Fˣ) : F), 1] = ((1 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)
  rw [Units.val_one, Units.val_one, ← diagonal_one]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem inverseTranspose_torusGL (b : Fˣ) :
    GeneralLinearGroup.inverseTranspose (torusGL b) = torusGL b⁻¹ := by
  apply Units.ext
  rw [GeneralLinearGroup.coe_inverseTranspose, coe_torusGL_inv, diagonal_transpose, coe_torusGL]

theorem eq_one_of_conjAut_torusGL_eq_one [Finite F] {b : Fˣ}
    (h : conjAut 3 F (torusGL b) = 1) : b = 1 := by
  obtain ⟨u, hu⟩ := (conjAut_eq_one_iff le_rfl _).1 h
  have hu' := congrArg (fun g : GL (Fin 3) F => (g : Matrix (Fin 3) (Fin 3) F)) hu
  have h00 := congrFun (congrFun hu' 0) 0
  have h11 := congrFun (congrFun hu' 1) 1
  simp [coe_torusGL, GeneralLinearGroup.scalar] at h00 h11
  exact Units.ext (by rw [h11, ← h00, Units.val_one])

variable [CharP F 2]

theorem fix_center_of_semilinear {A : GL (Fin 3) F} {σ : F ≃+* F}
    (h : ∀ c : F, conjAut 3 F A (fieldAut 3 F σ (proj 3 F (unipU F 0 0 c))) =
      proj 3 F (unipU F 0 0 c)) :
    σ = 1 ∧ (A : Matrix (Fin 3) (Fin 3) F) 1 0 = 0 ∧ (A : Matrix (Fin 3) (Fin 3) F) 2 0 = 0 ∧
      (A : Matrix (Fin 3) (Fin 3) F) 2 1 = 0 ∧
      (A : Matrix (Fin 3) (Fin 3) F) 2 2 = (A : Matrix (Fin 3) (Fin 3) F) 0 0 := by
  have key : ∀ c : F,
      (A : Matrix (Fin 3) (Fin 3) F) * (unipU F 0 0 (σ c) : Matrix (Fin 3) (Fin 3) F) =
        (unipU F 0 0 c : Matrix (Fin 3) (Fin 3) F) * A := by
    intro c
    have hc := h c
    rw [fieldAut_proj_unipU, map_zero] at hc
    exact mul_eq_mul_of_conjAut_proj_eq (by rw [trace_unipU, trace_unipU])
      (by rw [trace_unipU, three_eq_one_of_charTwo]; exact one_ne_zero) hc
  set M := (A : Matrix (Fin 3) (Fin 3) F) with hM
  have e : ∀ c : F, ∀ i j : Fin 3, M i j + (if j = 2 then σ c * M i 0 else 0) =
      M i j + if i = 0 then c * M 2 j else 0 := by
    intro c i j
    have := congrFun (congrFun (key c) i) j
    rwa [mul_unipU_center_apply, unipU_center_mul_apply] at this
  have e12 := e 1 1 2
  have e22 := e 1 2 2
  have e01 := e 1 0 1
  have e02 := e 1 0 2
  simp only [Fin.isValue, Fin.reduceEq, ite_true, ite_false, map_one, one_mul, add_zero]
    at e12 e22 e01 e02
  have h10 : M 1 0 = 0 := by linear_combination e12
  have h20 : M 2 0 = 0 := by linear_combination e22
  have h21 : M 2 1 = 0 := by linear_combination -e01
  have h22 : M 2 2 = M 0 0 := by linear_combination -e02
  have h00 : M 0 0 ≠ 0 := by
    intro h0
    apply Matrix.GeneralLinearGroup.det_ne_zero A
    rw [← hM, Matrix.det_fin_three, h0, h10, h20]
    ring
  refine ⟨RingEquiv.ext fun c => ?_, h10, h20, h21, h22⟩
  have hc := e c 0 2
  simp only [Fin.isValue, ite_true] at hc
  have : (σ c - c) * M 0 0 = 0 := by linear_combination hc + c * h22
  exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right h00)

theorem fix_lower_of_semilinear {A : GL (Fin 3) F} {σ : F ≃+* F}
    (h : ∀ c : F, conjAut 3 F A (fieldAut 3 F σ (projLevi F (vSL c))) = projLevi F (vSL c)) :
    (A : Matrix (Fin 3) (Fin 3) F) 0 1 = 0 ∧ (A : Matrix (Fin 3) (Fin 3) F) 0 2 = 0 ∧
      (A : Matrix (Fin 3) (Fin 3) F) 1 2 = 0 := by
  have key : (A : Matrix (Fin 3) (Fin 3) F) * (levi13 F (vSL (σ 1)) : Matrix (Fin 3) (Fin 3) F) =
      (levi13 F (vSL 1) : Matrix (Fin 3) (Fin 3) F) * A := by
    have hc := h 1
    rw [fieldAut_projLevi_vSL, projLevi_apply, projLevi_apply] at hc
    exact mul_eq_mul_of_conjAut_proj_eq (by rw [trace_projLevi_vSL, trace_projLevi_vSL])
      (by rw [trace_projLevi_vSL, three_eq_one_of_charTwo]; exact one_ne_zero) hc
  rw [map_one] at key
  set M := (A : Matrix (Fin 3) (Fin 3) F) with hM
  have e : ∀ i j : Fin 3, M i j + (if j = 0 then 1 * M i 2 else 0) =
      M i j + if i = 2 then 1 * M 0 j else 0 := by
    intro i j
    have := congrFun (congrFun key i) j
    rwa [mul_levi13_vSL_apply, levi13_vSL_mul_apply] at this
  have e00 := e 0 0
  have e10 := e 1 0
  have e21 := e 2 1
  simp only [Fin.isValue, Fin.reduceEq, ite_true, ite_false, one_mul, add_zero] at e00 e10 e21
  exact ⟨by linear_combination -e21, by linear_combination e00, by linear_combination e10⟩

theorem fix_center_of_graph {A : GL (Fin 3) F} {σ : F ≃+* F}
    (h : ∀ c : F, conjAut 3 F A (fieldAut 3 F σ (dualAut 3 F (proj 3 F (unipU F 0 0 c)))) =
      proj 3 F (unipU F 0 0 c)) :
    σ = 1 ∧ (A : Matrix (Fin 3) (Fin 3) F) 1 2 = 0 ∧ (A : Matrix (Fin 3) (Fin 3) F) 2 1 = 0 ∧
      (A : Matrix (Fin 3) (Fin 3) F) 2 2 = 0 ∧
      (A : Matrix (Fin 3) (Fin 3) F) 2 0 = (A : Matrix (Fin 3) (Fin 3) F) 0 2 := by
  have key : ∀ c : F,
      (A : Matrix (Fin 3) (Fin 3) F) * (levi13 F (vSL (σ c)) : Matrix (Fin 3) (Fin 3) F) =
        (unipU F 0 0 c : Matrix (Fin 3) (Fin 3) F) * A := by
    intro c
    have hc := h c
    rw [dualAut_proj_unipU_center, fieldAut_projLevi_vSL, projLevi_apply] at hc
    exact mul_eq_mul_of_conjAut_proj_eq (by rw [trace_projLevi_vSL, trace_unipU])
      (by rw [trace_unipU, three_eq_one_of_charTwo]; exact one_ne_zero) hc
  set M := (A : Matrix (Fin 3) (Fin 3) F) with hM
  have e : ∀ c : F, ∀ i j : Fin 3, M i j + (if j = 0 then σ c * M i 2 else 0) =
      M i j + if i = 0 then c * M 2 j else 0 := by
    intro c i j
    have := congrFun (congrFun (key c) i) j
    rwa [mul_levi13_vSL_apply, unipU_center_mul_apply] at this
  have e10 := e 1 1 0
  have e20 := e 1 2 0
  have e00 := e 1 0 0
  have e01 := e 1 0 1
  simp only [Fin.isValue, Fin.reduceEq, ite_true, ite_false, map_one, one_mul, add_zero]
    at e10 e20 e00 e01
  have h12 : M 1 2 = 0 := by linear_combination e10
  have h22 : M 2 2 = 0 := by linear_combination e20
  have h21 : M 2 1 = 0 := by linear_combination -e01
  have h20 : M 2 0 = M 0 2 := by linear_combination -e00
  have h02 : M 0 2 ≠ 0 := by
    intro h0
    apply Matrix.GeneralLinearGroup.det_ne_zero A
    rw [← hM, Matrix.det_fin_three, h20, h0, h21, h22]
    ring
  refine ⟨RingEquiv.ext fun c => ?_, h12, h21, h22, h20⟩
  have hc := e c 0 0
  simp only [Fin.isValue, ite_true] at hc
  have : (σ c - c) * M 0 2 = 0 := by linear_combination hc + c * h20
  exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right h02)

omit [CharP F 2] in
theorem exists_eq_scalar_mul_torusGL {A : GL (Fin 3) F}
    (h01 : (A : Matrix (Fin 3) (Fin 3) F) 0 1 = 0) (h02 : (A : Matrix (Fin 3) (Fin 3) F) 0 2 = 0)
    (h10 : (A : Matrix (Fin 3) (Fin 3) F) 1 0 = 0) (h12 : (A : Matrix (Fin 3) (Fin 3) F) 1 2 = 0)
    (h20 : (A : Matrix (Fin 3) (Fin 3) F) 2 0 = 0) (h21 : (A : Matrix (Fin 3) (Fin 3) F) 2 1 = 0)
    (h22 : (A : Matrix (Fin 3) (Fin 3) F) 2 2 = (A : Matrix (Fin 3) (Fin 3) F) 0 0) :
    ∃ a b : Fˣ, A = GeneralLinearGroup.scalar (Fin 3) a * torusGL b := by
  set M := (A : Matrix (Fin 3) (Fin 3) F) with hM
  have hdet : M.det ≠ 0 := Matrix.GeneralLinearGroup.det_ne_zero A
  rw [Matrix.det_fin_three, h01, h02, h10, h12, h20, h21, h22] at hdet
  have h00 : M 0 0 ≠ 0 := fun h => hdet (by rw [h]; ring)
  have h11 : M 1 1 ≠ 0 := fun h => hdet (by rw [h]; ring)
  refine ⟨Units.mk0 (M 0 0) h00, Units.mk0 (M 1 1 / M 0 0) (div_ne_zero h11 h00), ?_⟩
  apply Units.ext
  rw [Units.val_mul, coe_torusGL]
  ext i j
  rw [mul_diagonal]
  fin_cases i <;> fin_cases j <;>
    simp [GeneralLinearGroup.scalar, ← hM, h01, h02, h10, h12, h20, h21, h22]
  field_simp

theorem eq_one_of_inv_eq_self {b : Fˣ} (h : ((b⁻¹ : Fˣ) : F) = b) : b = 1 := by
  have hb0 : (b : F) ≠ 0 := b.ne_zero
  have h2 : ((b : F) - 1) ^ 2 = 0 := by
    have : (b : F) * b = 1 := by
      calc (b : F) * b = ((b⁻¹ : Fˣ) : F) * b := by rw [h]
        _ = 1 := by simp
    have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
    linear_combination this + (1 - (b : F)) * h2
  exact Units.ext (by rw [Units.val_one]; exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h2))

theorem eq_one_of_commute_of_fix_projLevi [Finite F] {b : Fˣ} (hb : b ≠ 1)
    {γ : MulAut (projectiveSL 3 F)} {k : ℕ} (hk : γ ^ 2 ^ k = 1)
    (hc : γ * conjAut 3 F (torusGL b) = conjAut 3 F (torusGL b) * γ)
    (hfix : ∀ B : SL2 F, γ (projLevi F B) = projLevi F B) : γ = 1 := by
  obtain ⟨A, σ, ε, hε, rfl⟩ := (automorphism_generation (K := F) (n := 3) le_rfl).2 γ
  have hz : ∀ c : F, (conjAut 3 F A * fieldAut 3 F σ * dualAut 3 F ^ ε)
      (proj 3 F (unipU F 0 0 c)) = proj 3 F (unipU F 0 0 c) := fun c => by
    rw [proj_unipU_center_eq_projLevi]
    exact hfix _
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hε with rfl | rfl
  ·
    simp only [pow_zero, mul_one] at hz hfix hk ⊢
    obtain ⟨hσ, h10, h20, h21, h22⟩ := fix_center_of_semilinear (A := A) (σ := σ) hz
    subst hσ
    simp only [map_one, mul_one] at hfix hk ⊢
    obtain ⟨h01, h02, h12⟩ := fix_lower_of_semilinear (A := A) (σ := 1)
      (fun c => by rw [map_one, MulAut.one_apply]; exact hfix _)
    obtain ⟨a, b', hA⟩ := exists_eq_scalar_mul_torusGL h01 h02 h10 h12 h20 h21 h22
    rw [hA, map_mul, conjAut_scalar, one_mul] at hk ⊢
    rw [← map_pow, torusGL_pow] at hk
    have h1 := eq_one_of_conjAut_torusGL_eq_one hk
    have hb' : b' = 1 := Units.ext (eq_of_pow_two_pow_eq (k := k)
      (by rw [← Units.val_pow_eq_pow_val, h1, Units.val_one, one_pow]))
    rw [hb', torusGL_one, map_one]
  ·
    simp only [pow_one] at hz hc
    obtain ⟨hσ, h12, h21, h22, h20⟩ := fix_center_of_graph (A := A) (σ := σ) hz
    subst hσ
    simp only [map_one, mul_one] at hc
    exfalso
    have htr := standard_automorphism_transport (K := F) (n := 3)
    have hδD : dualAut 3 F * conjAut 3 F (torusGL b) =
        conjAut 3 F (torusGL b⁻¹) * dualAut 3 F := by
      have h5 := htr.2.2.2.2.1 (torusGL b)
      rw [inverseTranspose_torusGL] at h5
      calc dualAut 3 F * conjAut 3 F (torusGL b)
          = dualAut 3 F * conjAut 3 F (torusGL b) * (dualAut 3 F * dualAut 3 F) := by
            rw [htr.2.2.2.1, mul_one]
        _ = conjAut 3 F (torusGL b⁻¹) * dualAut 3 F := by rw [← h5]; group
    have hkey : conjAut 3 F (A * torusGL b⁻¹) = conjAut 3 F (torusGL b * A) := by
      have h6 : conjAut 3 F A * conjAut 3 F (torusGL b⁻¹) * dualAut 3 F =
          conjAut 3 F (torusGL b) * conjAut 3 F A * dualAut 3 F := by
        rw [mul_assoc, ← hδD, ← mul_assoc, hc, mul_assoc]
      rw [map_mul, map_mul]
      exact mul_right_cancel h6
    have h1 : conjAut 3 F ((torusGL b * A)⁻¹ * (A * torusGL b⁻¹)) = 1 := by
      rw [map_mul, map_inv, hkey, inv_mul_cancel]
    obtain ⟨u, hu⟩ := (conjAut_eq_one_iff le_rfl _).1 h1
    have hmat := congrArg (fun g : GL (Fin 3) F => (g : Matrix (Fin 3) (Fin 3) F))
      (inv_mul_eq_iff_eq_mul.1 hu)
    simp only [Units.val_mul, coe_torusGL] at hmat
    have e20 := congrFun (congrFun hmat 2) 0
    have e11 := congrFun (congrFun hmat 1) 1
    simp [mul_diagonal, diagonal_mul, GeneralLinearGroup.scalar] at e20 e11
    set M := (A : Matrix (Fin 3) (Fin 3) F) with hM
    have hdet : M.det ≠ 0 := Matrix.GeneralLinearGroup.det_ne_zero A
    rw [Matrix.det_fin_three, h12, h21, h22, h20] at hdet
    have h02 : M 0 2 ≠ 0 := fun h => hdet (by rw [h]; ring)
    have h11 : M 1 1 ≠ 0 := fun h => hdet (by rw [h]; ring)
    have hu1 : (u : F) = 1 := by
      rw [h20] at e20
      have : M 0 2 * (1 - u) = 0 := by linear_combination e20
      exact (sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left h02)).symm
    rw [hu1, mul_one] at e11
    have hbb : ((b⁻¹ : Fˣ) : F) = b := by
      have : M 1 1 * (((b : F))⁻¹ - b) = 0 := by linear_combination e11
      rw [Units.val_inv_eq_inv_val]
      exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left h11)
    exact hb (eq_one_of_inv_eq_self hbb)

omit [CharP F 2] in
theorem map_projLevi_mem_of_commute [Group.IsPerfect (SL2 F)] {b : Fˣ} (hb : b ≠ 1)
    {γ : MulAut (projectiveSL 3 F)}
    (hc : γ * conjAut 3 F (torusGL b) = conjAut 3 F (torusGL b) * γ) (B : SL2 F) :
    γ (projLevi F B) ∈ (projLevi F).range := by
  have hfix : (fixTorus F b).map (γ : projectiveSL 3 F →* projectiveSL 3 F) ≤ fixTorus F b := by
    rintro _ ⟨p, hp, rfl⟩
    have hp' : conjAut 3 F (torusGL b) p = p := hp
    show conjAut 3 F (torusGL b) (γ p) = γ p
    have h := congrArg (fun φ : MulAut (projectiveSL 3 F) => φ p) hc
    simp only [MulAut.mul_apply] at h
    rw [← h, hp']
  have hle : (projLevi F).range.map (γ : projectiveSL 3 F →* projectiveSL 3 F) ≤
      (projLevi F).range := by
    rw [← commutator_fixTorus hb, Subgroup.map_commutator]
    exact Subgroup.commutator_mono hfix hfix
  exact hle ⟨_, ⟨B, rfl⟩, rfl⟩

omit [CharP F 2] in
theorem conj_map_eq {G : Type*} [Group G] (φ : MulAut G) (x : G) :
    MulAut.conj (φ x) = φ * MulAut.conj x * φ⁻¹ := by
  ext y
  simp only [MulAut.conj_apply, MulAut.mul_apply, map_mul, MulAut.apply_inv_self, map_inv]

omit [CharP F 2] in
theorem unipU_center_pow (c : F) (n : ℕ) : unipU F 0 0 c ^ n = unipU F 0 0 (n * c) := by
  induction n with
  | zero => simp [unipU_zero]
  | succ n ih =>
    rw [pow_succ, ih, unipU_mul]
    congr 1 <;> push_cast <;> ring

theorem natCast_eq_one_of_odd {N : ℕ} (hN : Odd N) : (N : F) = 1 := by
  obtain ⟨k, rfl⟩ := hN
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  push_cast
  rw [h2, zero_mul, zero_add]

theorem exists_eq_conj_torus [Finite F] {α : MulAut (projectiveSL 3 F)} (hα : Odd (orderOf α))
    (hZ : ∀ z ∈ projCenterW F, α z = z)
    (hU : ∃ u ∈ projUnip F, α u * u⁻¹ ∉ projCenterW F) :
    ∃ (v : projectiveSL 3 F) (b : Fˣ), b ≠ 1 ∧
      α = MulAut.conj v * conjAut 3 F (torusGL b) * (MulAut.conj v)⁻¹ := by
  obtain ⟨A, σ, rfl⟩ := mem_semilinearAutGroup_iff.1
    (UnbalancedCatalog.EvenLinearSL.mem_semilinearAutGroup_of_odd le_rfl hα)
  obtain ⟨hσ, h10, h20, h21, h22⟩ := fix_center_of_semilinear (A := A) (σ := σ)
    (fun c => hZ _ (mem_projCenterW.2 ⟨c, rfl⟩))
  subst hσ
  simp only [map_one, mul_one] at hα hU ⊢
  set M := (A : Matrix (Fin 3) (Fin 3) F) with hM
  have hdet : M.det ≠ 0 := Matrix.GeneralLinearGroup.det_ne_zero A
  rw [Matrix.det_fin_three, h10, h20, h21, h22] at hdet
  have hp : M 0 0 ≠ 0 := fun h => hdet (by rw [h]; ring)
  have hr : M 1 1 ≠ 0 := fun h => hdet (by rw [h]; ring)
  have hpr : M 1 1 ≠ M 0 0 := by
    intro hrp
    obtain ⟨u, hu, hnot⟩ := hU
    apply hnot
    set n := unipU F (M 0 1 / M 0 0) (M 1 2 / M 0 0) (M 0 2 / M 0 0) with hn
    have hA : A = GeneralLinearGroup.scalar (Fin 3) (Units.mk0 (M 0 0) hp) *
        Matrix.SpecialLinearGroup.toGL n := by
      apply Units.ext
      rw [Units.val_mul, Matrix.SpecialLinearGroup.coe_GL_coe_matrix, hn, coe_unipU]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [GeneralLinearGroup.scalar, ← hM, h10, h20, h21, h22,
        hrp] <;> field_simp
    rw [hA, map_mul, conjAut_scalar, one_mul, conjAut_toGL, MulAut.conj_apply]
    exact commutatorElement_mem_projCenterW (mem_projUnip.2 ⟨_, _, _, rfl⟩) hu
  have hpr' : M 0 0 - M 1 1 ≠ 0 := sub_ne_zero.2 (Ne.symm hpr)
  have hrp' : M 1 1 - M 0 0 ≠ 0 := sub_ne_zero.2 hpr
  obtain ⟨s₁, hs₁⟩ : ∃ s : F, s = M 0 1 / (M 0 0 - M 1 1) := ⟨_, rfl⟩
  obtain ⟨s₂, hs₂⟩ : ∃ s : F, s = M 1 2 / (M 1 1 - M 0 0) := ⟨_, rfl⟩
  obtain ⟨e, he⟩ : ∃ e : F, e = (M 0 2 + s₁ * M 1 2) / M 0 0 := ⟨_, rfl⟩
  set β : Fˣ := Units.mk0 (M 1 1 / M 0 0) (div_ne_zero hr hp) with hβ
  have hβ1 : β ≠ 1 := by
    intro h
    have h' := congrArg Units.val h
    rw [hβ, Units.val_mk0, Units.val_one, div_eq_one_iff_eq hp] at h'
    exact hpr h'
  set X : GL (Fin 3) F := GeneralLinearGroup.scalar (Fin 3) (Units.mk0 (M 0 0) hp) * torusGL β *
    Matrix.SpecialLinearGroup.toGL (unipU F 0 0 e) with hX
  have hkey : Matrix.SpecialLinearGroup.toGL (unipU F s₁ s₂ 0) * A =
      X * Matrix.SpecialLinearGroup.toGL (unipU F s₁ s₂ 0) := by
    apply Units.ext
    rw [hX, Units.val_mul, Units.val_mul, Units.val_mul, Units.val_mul,
      Matrix.SpecialLinearGroup.coe_GL_coe_matrix, Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
      coe_torusGL, coe_unipU, coe_unipU, ← hM]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [GeneralLinearGroup.scalar, Matrix.mul_apply, Fin.sum_univ_three, h10, h20, h21, h22,
        β] <;> field_simp
    · rw [hs₁]
      field_simp
      ring
    · rw [he]
      field_simp
    · rw [hs₂]
      field_simp
      ring
  have hA : A = (Matrix.SpecialLinearGroup.toGL (unipU F s₁ s₂ 0))⁻¹ * X *
      Matrix.SpecialLinearGroup.toGL (unipU F s₁ s₂ 0) := by
    rw [mul_assoc, ← hkey, ← mul_assoc, inv_mul_cancel, one_mul]
  set g := proj 3 F (unipU F s₁ s₂ 0) with hg
  set z := proj 3 F (unipU F 0 0 e) with hz
  have hcX : conjAut 3 F X = conjAut 3 F (torusGL β) * MulAut.conj z := by
    rw [hX, map_mul, map_mul, conjAut_scalar, one_mul, conjAut_toGL]
  have hα' : conjAut 3 F A =
      (MulAut.conj g)⁻¹ * (conjAut 3 F (torusGL β) * MulAut.conj z) * MulAut.conj g := by
    rw [hA, map_mul, map_mul, map_inv, conjAut_toGL, hcX]
  have hcomm : Commute (conjAut 3 F (torusGL β)) (MulAut.conj z) := by
    have hfz : conjAut 3 F (torusGL β) z = z := by
      rw [hz, proj_unipU_center_eq_projLevi]
      exact conjAut_torusGL_projLevi β _
    have h := conj_map_eq (conjAut 3 F (torusGL β)) z
    rw [hfz] at h
    rw [Commute, SemiconjBy, ← mul_inv_eq_iff_eq_mul, ← h]
  have he0 : e = 0 := by
    set N := orderOf (conjAut 3 F A) with hN
    have h1 : (conjAut 3 F (torusGL β) * MulAut.conj z) ^ N = 1 := by
      have h2 := pow_orderOf_eq_one (conjAut 3 F A)
      rw [← hN, hα', ← inv_inv (MulAut.conj g), inv_inv, conj_pow] at h2
      have h3 := congrArg (fun φ => MulAut.conj g * φ * (MulAut.conj g)⁻¹) h2
      simpa [mul_assoc] using h3
    rw [hcomm.mul_pow, ← map_pow, torusGL_pow, ← map_pow, hz, ← map_pow, unipU_center_pow,
      ← conjAut_toGL, ← map_mul] at h1
    obtain ⟨u, hu⟩ := (conjAut_eq_one_iff le_rfl _).1 h1
    have h4 := congrFun (congrFun (congrArg (fun x : GL (Fin 3) F =>
      (x : Matrix (Fin 3) (Fin 3) F)) hu) 0) 2
    simp [Units.val_mul, coe_torusGL, coe_unipU, Matrix.mul_apply, Fin.sum_univ_three,
      GeneralLinearGroup.scalar] at h4
    rw [natCast_eq_one_of_odd hα] at h4
    exact h4.resolve_left one_ne_zero
  have hz1 : MulAut.conj z = 1 := by
    rw [hz, he0, unipU_zero, map_one, map_one]
  refine ⟨g⁻¹, β, hβ1, ?_⟩
  rw [hα', hz1, mul_one, map_inv, inv_inv]

omit [CharP F 2] in
theorem commutatorElement_mem_linearAutGroup [Finite F] {m : ℕ} (hm : 1 ≤ m)
    (hK : Nat.card F = 2 ^ m) (a b : MulAut (projectiveSL 3 F)) :
    ⁅a, b⁆ ∈ linearAutGroup 3 F := by
  have : CharP F 2 := finite_field_prime_power_characteristic Nat.prime_two hm hK
  rw [commutatorElement_def]
  exact (CFSG.RankThree.LinearDescent.higher_linear_prime_semilinear_field_descent
    Nat.prime_two hm le_rfl hK).2.2.2.2.2.2.1 a b

omit [CharP F 2] in
theorem mem_inner_of_mem_linearAutGroup [Finite F] {δ : MulAut (projectiveSL 3 F)}
    (hδ : δ ∈ linearAutGroup 3 F) {k : ℕ} (hk : δ ^ 2 ^ k = 1) :
    δ ∈ (MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F)).range :=
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag.mem_range_conj_of_mem_linearAutGroup_of_coprime hδ
    (Nat.Coprime.pow_left k (by norm_num)) hk

omit [CharP F 2] in
theorem conj_injective_projectiveSL :
    Function.Injective (MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F)) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro g hg
  have hz : g ∈ center (projectiveSL 3 F) := by
    rw [mem_center_iff]
    intro y
    have h := congrArg (fun φ : MulAut (projectiveSL 3 F) => φ y) (MonoidHom.mem_ker.1 hg)
    simp only [MulAut.conj_apply, MulAut.one_apply] at h
    calc y * g = g * y * g⁻¹ * g := by rw [h]
      _ = g * y := by group
  rwa [RankTwoHypIIL3.center_projectiveSL_three_eq_bot] at hz

theorem exists_eq_conj_x0 [Finite F] {τ : MulAut (projectiveSL 3 F)}
    (hτ : τ ∈ (MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F)).range)
    (h2 : τ * τ = 1) (h1 : τ ≠ 1) :
    ∃ γ : MulAut (projectiveSL 3 F), τ = γ * MulAut.conj (x0 F) * γ⁻¹ := by
  obtain ⟨p, rfl⟩ := hτ
  have hp : p * p = 1 := conj_injective_projectiveSL (by rw [map_mul, h2, map_one])
  have hp1 : p ≠ 1 := fun h => h1 (by rw [h, map_one])
  obtain ⟨y, hy⟩ := exists_conj_eq_x0 hp hp1
  refine ⟨MulAut.conj y⁻¹, ?_⟩
  rw [← hy, ← map_inv, ← map_mul, ← map_mul, inv_inv]
  congr 1
  group

theorem mem_map_projUnip_of_commute {σ : MulAut (projectiveSL 3 F)}
    (hσ : σ ∈ (MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F)).range)
    (hc : σ * MulAut.conj (x0 F) = MulAut.conj (x0 F) * σ) {k : ℕ} (hk : σ ^ 2 ^ k = 1) :
    σ ∈ (projUnip F).map (MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F)) := by
  obtain ⟨y, rfl⟩ := hσ
  refine ⟨y, mem_projUnip_of_commute_x0 (k := k) ?_ ?_, rfl⟩
  · exact conj_injective_projectiveSL (by rw [map_mul, map_mul]; exact hc)
  · exact conj_injective_projectiveSL (by rw [map_pow, hk, map_one])

end CFSG.ComponentClassification.RankTwoL3Even
