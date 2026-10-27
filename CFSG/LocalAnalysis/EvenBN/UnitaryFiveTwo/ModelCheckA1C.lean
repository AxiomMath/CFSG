module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.ModelCheckA1
import all CFSG.Fischer.F4

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup CFSG.Fischer Matrix Certificates.U52Yamada

theorem entry_eq_of_isA₁Shape {M : Matrix (Fin 5) (Fin 5) F4} (h : IsA₁Shape (M - 1))
    {i j : Fin 5} (hij : ¬ ((j = 0 ∧ i ≠ 0) ∨ (i = 4 ∧ j ≠ 4))) :
    M i j = (1 : Matrix (Fin 5) (Fin 5) F4) i j := by
  have := h i j hij
  rwa [Matrix.sub_apply, sub_eq_zero] at this

theorem cvec_conj {s a : SU52} (hs : s * zSU = zSU * s) (ha : a ∈ A₁sub) :
    (blk3 (mat s)).mulVec (cvec (mat a)) = mat s 0 0 • cvec (mat (s * a * s⁻¹)) := by
  have hN := isA₁Shape_of_mem_A₁sub ha
  have hN' := isA₁Shape_of_mem_A₁sub (conj_mem_A₁sub_of_comm_z hs ha)
  obtain ⟨⟨-, h4⟩, -⟩ := isBlk_of_comm_z hs
  have e : mat (s * a * s⁻¹) * mat s = mat s * mat a := by
    rw [← mat_mul, ← mat_mul, inv_mul_cancel_right]
  have a00 := entry_eq_of_isA₁Shape hN (i := 0) (j := 0) (by decide)
  have s14 := h4 1 (by decide)
  have s24 := h4 2 (by decide)
  have s34 := h4 3 (by decide)
  funext i
  fin_cases i
  · have ei := congrFun (congrFun e 1) 0
    have b1 := entry_eq_of_isA₁Shape hN' (i := 1) (j := 1) (by decide)
    have b2 := entry_eq_of_isA₁Shape hN' (i := 1) (j := 2) (by decide)
    have b3 := entry_eq_of_isA₁Shape hN' (i := 1) (j := 3) (by decide)
    have b4 := entry_eq_of_isA₁Shape hN' (i := 1) (j := 4) (by decide)
    simp only [Matrix.mul_apply, Fin.sum_univ_five] at ei
    rw [b1, b2, b3, b4, a00, s14] at ei
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, blk3, cvec, ι3] at ei ⊢
    linear_combination ei.symm
  · have ei := congrFun (congrFun e 2) 0
    have b1 := entry_eq_of_isA₁Shape hN' (i := 2) (j := 1) (by decide)
    have b2 := entry_eq_of_isA₁Shape hN' (i := 2) (j := 2) (by decide)
    have b3 := entry_eq_of_isA₁Shape hN' (i := 2) (j := 3) (by decide)
    have b4 := entry_eq_of_isA₁Shape hN' (i := 2) (j := 4) (by decide)
    simp only [Matrix.mul_apply, Fin.sum_univ_five] at ei
    rw [b1, b2, b3, b4, a00, s24] at ei
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, blk3, cvec, ι3] at ei ⊢
    linear_combination ei.symm
  · have ei := congrFun (congrFun e 3) 0
    have b1 := entry_eq_of_isA₁Shape hN' (i := 3) (j := 1) (by decide)
    have b2 := entry_eq_of_isA₁Shape hN' (i := 3) (j := 2) (by decide)
    have b3 := entry_eq_of_isA₁Shape hN' (i := 3) (j := 3) (by decide)
    have b4 := entry_eq_of_isA₁Shape hN' (i := 3) (j := 4) (by decide)
    simp only [Matrix.mul_apply, Fin.sum_univ_five] at ei
    rw [b1, b2, b3, b4, a00, s34] at ei
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, blk3, cvec, ι3] at ei ⊢
    linear_combination ei.symm

theorem comm_zSU_of_mem {s : SU52} (h : zSU⁻¹ * (s * zSU * s⁻¹) ∈ ZX₄sub) :
    s * zSU = zSU * s := by
  have hzZ : s * zSU * s⁻¹ ∈ ZX₄sub := by
    have := mul_mem zSU_mem h
    rwa [mul_inv_cancel_left] at this
  obtain ⟨α, β, hα, hm⟩ := mem_x₄Sub.1 hzZ
  subst hα
  rcases (show ∀ b : F4, (0 : F4) * bar 0 = b + bar b → b = 0 ∨ b = 1 by decide) β
      (x₄_coord_rel hm) with rfl | rfl
  · exfalso
    apply zSU_ne_one
    have e1 : s * zSU * s⁻¹ = 1 := ext_mat (by rw [hm, mat_one]; decide)
    calc zSU = s⁻¹ * (s * zSU * s⁻¹) * s := by group
      _ = 1 := by rw [e1]; group
  · have e1 : s * zSU * s⁻¹ = zSU := ext_mat (by rw [hm, mat_zSU])
    calc s * zSU = s * zSU * s⁻¹ * s := by group
      _ = zSU * s := by rw [e1]

theorem mem_A₁sub_of_conj_mem {s : SU52} (h : ∀ a ∈ A₁sub, a⁻¹ * (s * a * s⁻¹) ∈ ZX₄sub) :
    s ∈ A₁sub := by
  have hs := comm_zSU_of_mem (h zSU (X₄sub_le_A₁sub' (ZX₄sub_le_X₄sub zSU_mem)))
  obtain ⟨⟨h0, h4⟩, h04⟩ := isBlk_of_comm_z hs
  have hB : ∀ a ∈ A₁sub, (blk3 (mat s)).mulVec (cvec (mat a)) = mat s 0 0 • cvec (mat a) :=
    fun a ha => by
      rw [cvec_conj hs ha, (inv_mul_mem_ZX₄sub_iff ha (conj_mem_A₁sub_of_comm_z hs ha)).1
        (h a ha)]
  have c0 := hB (x₂SU 1) (X₂sub_le_A₁sub (x₂SU_mem 1))
  have c1 := hB (x₄SU 1 F4.ω one_omega_rel) (X₄sub_le_A₁sub' (x₄SU_mem _ _ _))
  have c2 := hB (x₃SU 1) (X₃sub_le_A₁sub (x₃SU_mem 1))
  rw [mat_x₂SU, cvec_x₂] at c0
  rw [mat_x₄SU, cvec_x₄] at c1
  rw [mat_x₃SU, cvec_x₃] at c2
  have m11 : mat s 1 1 = mat s 0 0 := by
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three, blk3, ι3] using congrFun c0 0
  have m21 : mat s 2 1 = 0 := by
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three, blk3, ι3] using congrFun c0 1
  have m31 : mat s 3 1 = 0 := by
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three, blk3, ι3] using congrFun c0 2
  have m12 : mat s 1 2 = 0 := by
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three, blk3, ι3] using congrFun c1 0
  have m22 : mat s 2 2 = mat s 0 0 := by
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three, blk3, ι3] using congrFun c1 1
  have m32 : mat s 3 2 = 0 := by
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three, blk3, ι3] using congrFun c1 2
  have m13 : mat s 1 3 = 0 := by
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three, blk3, ι3] using congrFun c2 0
  have m23 : mat s 2 3 = 0 := by
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three, blk3, ι3] using congrFun c2 1
  have m33 : mat s 3 3 = mat s 0 0 := by
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three, blk3, ι3] using congrFun c2 2
  have r1 := h0 1 (by decide)
  have r2 := h0 2 (by decide)
  have r3 := h0 3 (by decide)
  have r4 := h0 4 (by decide)
  have k1 := h4 1 (by decide)
  have k2 := h4 2 (by decide)
  have k3 := h4 3 (by decide)
  have hlt : (mat s).IsLowerTriangular := fun i j hij => by
    have hij' : i < j := OrderDual.toDual_lt_toDual.1 hij
    fin_cases i <;> fin_cases j <;> simp [r1, r2, r3, r4, k1, k2, k3, m12, m13, m23] at hij' ⊢
  have hdet := Matrix.det_of_isLowerTriangular (mat s) hlt
  rw [(mem_SU52.1 s.2).2, Fin.prod_univ_five, m11, m22, m33, ← h04] at hdet
  have hl : mat s 0 0 = 1 := eq_one_of_pow_five _ (by rw [hdet]; ring)
  have hl4 : mat s 4 4 = 1 := h04 ▸ hl
  refine mem_A₁sub_of_shape fun i j hij => ?_
  rw [Matrix.sub_apply]
  fin_cases i <;> fin_cases j <;>
    simp [r1, r2, r3, r4, k1, k2, k3, m11, m12, m13, m21, m22, m23, m31, m32, m33, hl, hl4]
      at hij ⊢

theorem not_conj_fld_mem (s : SU52) :
    ¬ ∀ a ∈ A₁sub, a⁻¹ * (s * fld a * s⁻¹) ∈ ZX₄sub := by
  intro h
  have hz := h zSU (X₄sub_le_A₁sub' (ZX₄sub_le_X₄sub zSU_mem))
  rw [fld_zSU] at hz
  have hs := comm_zSU_of_mem hz
  obtain ⟨⟨h0, -⟩, -⟩ := isBlk_of_comm_z hs
  have key : ∀ c : F4, (blk3 (mat s)).mulVec (cvec (mat (x₂SU (bar c)))) =
      mat s 0 0 • cvec (mat (x₂SU c)) := fun c => by
    have hA : x₂SU (bar c) ∈ A₁sub := X₂sub_le_A₁sub (x₂SU_mem _)
    have e := h (x₂SU c) (X₂sub_le_A₁sub (x₂SU_mem c))
    rw [fld_x₂SU] at e
    rw [cvec_conj hs hA, (inv_mul_mem_ZX₄sub_iff (X₂sub_le_A₁sub (x₂SU_mem c))
      (conj_mem_A₁sub_of_comm_z hs hA)).1 e]
  have k1 := congrFun (key 1) 0
  have kω := congrFun (key F4.ω) 0
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, blk3, ι3, cvec_x₂, bar_ω] at k1 kω
  have s00 : mat s 0 0 = 0 := by linear_combination kω - (F4.ω + 1) * k1
  have hrow : ∀ j, mat s 0 j = 0 := fun j => by
    by_cases hj : j = 0
    · rw [hj, s00]
    · exact h0 j hj
  have hdet := (mem_SU52.1 s.2).2
  rw [Matrix.det_succ_row_zero] at hdet
  simp [hrow] at hdet

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
