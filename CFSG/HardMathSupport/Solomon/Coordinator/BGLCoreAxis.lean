module

public import CFSG.HardMathSupport.Solomon.Coordinator.BGLCoreRat
public import CFSG.HardMathSupport.Solomon.Coordinator.BGLCoreLevi

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.BGL

open Matrix CFSG.LargeExtraspecial.A2Mod
open scoped commutatorElement

variable {F : Type} [Field F] {σ : F ≃+* F}

section Axis

variable [Finite F] (hr : (orderOf σ).Prime) {H : Subgroup (SpecialLinearGroup (Fin 3) F)}
  (hA : fixSL3 σ ≤ H)
include hr hA

theorem top_le_of_tv_rat_axis {x φ : Fin 3 → F} (hφ : IsRat σ φ) (hφ0 : φ ≠ 0)
    (hxφ : φ ⬝ᵥ x = 0) (hx : ¬ IsRat σ x) (hmem : tv x φ ∈ H) : ⊤ ≤ H := by
  obtain ⟨a, ha, hrow⟩ := exists_ratGL_row2 hφ hφ0
  apply top_le_of_top_le_map (a := a)
  have hA' : fixSL3 σ ≤ H.map (conjGL3 a) := by
    rw [← map_conjGL3_fixSL3 ha]
    exact Subgroup.map_mono hA
  have hmem' : conjGL3 a (tv x φ) ∈ H.map (conjGL3 a) := ⟨_, hmem, rfl⟩
  rw [conjGL3_tv a hxφ] at hmem'
  have hφa : φ ᵥ* ((a⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = Pi.single 2 1 := by
    rw [← hrow, Matrix.vecMul_vecMul, coe_mul_inv, Matrix.vecMul_one]
  rw [hφa] at hmem'
  set y := (a : Matrix (Fin 3) (Fin 3) F) *ᵥ x with hy
  have hy2 : y 2 = 0 := by
    have h : (Pi.single 2 (1 : F) : Fin 3 → F) ⬝ᵥ y = 0 := by
      rw [hy, Matrix.dotProduct_mulVec, hrow, hxφ]
    simpa [dotProduct, Fin.sum_univ_three] using h
  rw [tv_col2 y hy2] at hmem'
  refine top_le_of_dualLevi hA' hr hmem' ?_
  rintro ⟨h0, h1⟩
  apply hx
  have hyr : IsRat σ y := by
    intro i
    fin_cases i
    · exact h0
    · exact h1
    · change σ (y 2) = y 2
      rw [hy2, map_zero]
  have hxy : x = ((a⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ y := by
    rw [hy, Matrix.mulVec_mulVec, coe_inv_mul, Matrix.one_mulVec]
  rw [hxy]
  exact IsRatM.mulVec (IsRatM.inv ha) hyr

theorem top_le_of_tv_rat_center {x φ : Fin 3 → F} (hx : IsRat σ x) (hx0 : x ≠ 0)
    (hxφ : φ ⬝ᵥ x = 0) (hφ : ¬ IsRat σ φ) (hmem : tv x φ ∈ H) : ⊤ ≤ H := by
  obtain ⟨m, hm, hcol⟩ := exists_ratGL_col0 hx hx0
  have hm' : m⁻¹ ∈ ratGL σ := (ratGL σ).inv_mem hm
  apply top_le_of_top_le_map (a := m⁻¹)
  have hA' : fixSL3 σ ≤ H.map (conjGL3 m⁻¹) := by
    rw [← map_conjGL3_fixSL3 hm']
    exact Subgroup.map_mono hA
  have hmem' : conjGL3 m⁻¹ (tv x φ) ∈ H.map (conjGL3 m⁻¹) := ⟨_, hmem, rfl⟩
  rw [conjGL3_tv m⁻¹ hxφ, inv_inv] at hmem'
  have hx' : ((m⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x = Pi.single 0 1 := by
    rw [← hcol, Matrix.mulVec_mulVec, coe_inv_mul, Matrix.one_mulVec]
  rw [hx'] at hmem'
  set y := φ ᵥ* (m : Matrix (Fin 3) (Fin 3) F) with hy
  have hy0 : y 0 = 0 := by
    have h : y ⬝ᵥ (Pi.single 0 (1 : F) : Fin 3 → F) = 0 := by
      rw [hy, ← Matrix.dotProduct_mulVec, hcol, hxφ]
    simpa [dotProduct, Fin.sum_univ_three] using h
  rw [tv_row0 y hy0] at hmem'
  refine top_le_of_levi hA' hr hmem' ?_
  rintro ⟨h1, h2⟩
  apply hφ
  have hyr : IsRat σ y := by
    intro i
    fin_cases i
    · change σ (y 0) = y 0
      rw [hy0, map_zero]
    · exact h1
    · exact h2
  have hφy : φ = y ᵥ* ((m⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
    rw [hy, Matrix.vecMul_vecMul, coe_mul_inv, Matrix.vecMul_one]
  rw [hφy]
  exact IsRat.vecMul hyr (IsRatM.inv hm)

end Axis

theorem expand_aux {R : Type*} [Ring R] {X Y : R} (hXX : X * X = 0) (hYY : Y * Y = 0)
    (hYX : Y * X = 0) : (1 + X) * (1 + Y) * (1 - X) * (1 - Y) = 1 + X * Y := by
  have e1 : (1 + X) * (1 + Y) * (1 - X) = 1 + Y + X * Y - X * X - Y * X - X * (Y * X) := by
    noncomm_ring
  have e2 : (1 + Y + X * Y) * (1 - Y) = 1 + X * Y - Y * Y - X * (Y * Y) := by
    noncomm_ring
  rw [e1, hXX, hYX, mul_zero, sub_zero, sub_zero, sub_zero, e2, hYY, mul_zero, sub_zero,
    sub_zero]

theorem vecMulVec_neg_right (u w : Fin 3 → F) : vecMulVec u (-w) = -vecMulVec u w := by
  ext i j
  simp [vecMulVec_apply]

theorem vecMulVec_smul_left' (c : F) (u w : Fin 3 → F) :
    vecMulVec (c • u) w = c • vecMulVec u w := by
  ext i j
  simp [vecMulVec_apply, mul_assoc]

theorem vecMulVec_smul_right' (c : F) (u w : Fin 3 → F) :
    vecMulVec u (c • w) = c • vecMulVec u w := by
  ext i j
  simp [vecMulVec_apply, mul_left_comm]

theorem vecMulVec_zero_right' (u : Fin 3 → F) : vecMulVec u (0 : Fin 3 → F) = 0 := by
  ext i j
  simp [vecMulVec_apply]

theorem commutator_tv {u w a b : Fin 3 → F} (hwu : w ⬝ᵥ u = 0) (hba : b ⬝ᵥ a = 0)
    (hbu : b ⬝ᵥ u = 0) : ⁅tv u w, tv a b⁆ = tv ((w ⬝ᵥ a) • u) b := by
  have hn1 : (-w) ⬝ᵥ u = 0 := by rw [neg_dotProduct, hwu, neg_zero]
  have hn2 : (-b) ⬝ᵥ a = 0 := by rw [neg_dotProduct, hba, neg_zero]
  have hres : b ⬝ᵥ ((w ⬝ᵥ a) • u) = 0 := by rw [dotProduct_smul, hbu, smul_zero]
  rw [commutatorElement_def, tv_inv hwu, tv_inv hba]
  apply Subtype.ext
  simp only [SpecialLinearGroup.coe_mul]
  rw [coe_tv hwu, coe_tv hba, coe_tv hn1, coe_tv hn2, coe_tv hres, vecMulVec_neg_right,
    vecMulVec_neg_right, ← sub_eq_add_neg, ← sub_eq_add_neg]
  have hXX : vecMulVec u w * vecMulVec u w = 0 := by
    rw [vecMulVec_mul_vecMulVec, hwu, zero_smul, vecMulVec_zero_right']
  have hYY : vecMulVec a b * vecMulVec a b = 0 := by
    rw [vecMulVec_mul_vecMulVec, hba, zero_smul, vecMulVec_zero_right']
  have hYX : vecMulVec a b * vecMulVec u w = 0 := by
    rw [vecMulVec_mul_vecMulVec, hbu, zero_smul, vecMulVec_zero_right']
  rw [expand_aux hXX hYY hYX, vecMulVec_mul_vecMulVec, vecMulVec_smul_right',
    vecMulVec_smul_left']

end CFSG.HardMathSupport.Solomon.Coordinator.BGL
