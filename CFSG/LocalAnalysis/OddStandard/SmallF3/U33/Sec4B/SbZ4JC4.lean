module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4JC3

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {H : Type} [Group H] [Finite H]

namespace ZJBase

variable {Q Y V V' B : Subgroup H} {ρ t τ l y z v₁ v₂ : H}
variable (h : ZJBase Q Y V V' B ρ t τ l y z v₁ v₂) include h

theorem mat_t : zjMat y z v₁ v₂ t = ZJFin.T := by
  have hyV : y ∈ V := by
    rw [h.V_eq]
    exact Subgroup.subset_closure (by simp)
  have hzV : z ∈ V := by
    rw [h.V_eq]
    exact Subgroup.subset_closure (by simp)
  have hty : t * y * t⁻¹ = y := by
    rw [h.V_cent_t y hyV]
    group
  have htz : t * z * t⁻¹ = z := by
    rw [h.V_cent_t z hzV]
    group
  have hvy5 : v₁ * y = zjVec y z v₁ v₂ 5 := by
    have hx := h.vec_xor (n := 4) (m := 1) (by norm_num) (by norm_num)
    rw [show (4 : ℕ) ^^^ 1 = 5 by decide] at hx
    calc v₁ * y = zjVec y z v₁ v₂ 4 * zjVec y z v₁ v₂ 1 := by
          rw [(h.vec_basis).2.2.2.1, (h.vec_basis).2.1]
      _ = zjVec y z v₁ v₂ 5 := hx.symm
  have hvz11 : v₂ * (y * z) = zjVec y z v₁ v₂ 11 := by
    have hyz3 : y * z = zjVec y z v₁ v₂ 3 := by
      have hx := h.vec_xor (n := 1) (m := 2) (by norm_num) (by norm_num)
      rw [show (1 : ℕ) ^^^ 2 = 3 by decide] at hx
      calc y * z = zjVec y z v₁ v₂ 1 * zjVec y z v₁ v₂ 2 := by
            rw [(h.vec_basis).2.1, (h.vec_basis).2.2.1]
        _ = zjVec y z v₁ v₂ 3 := hx.symm
    have hx := h.vec_xor (n := 8) (m := 3) (by norm_num) (by norm_num)
    rw [show (8 : ℕ) ^^^ 3 = 11 by decide] at hx
    calc v₂ * (y * z) = zjVec y z v₁ v₂ 8 * zjVec y z v₁ v₂ 3 := by
          rw [(h.vec_basis).2.2.2.2, hyz3]
      _ = zjVec y z v₁ v₂ 11 := hx.symm
  have key_y : zjCode y z v₁ v₂ (t * y * t⁻¹) = 1 := by
    rw [hty]
    exact (by simpa [(h.vec_basis).2.1] using h.code_vec (n := 1) (by norm_num))
  have key_z : zjCode y z v₁ v₂ (t * z * t⁻¹) = 2 := by
    rw [htz]
    exact (by simpa [(h.vec_basis).2.2.1] using h.code_vec (n := 2) (by norm_num))
  have key_v₁ : zjCode y z v₁ v₂ (t * v₁ * t⁻¹) = 5 := by
    rw [h.t_v₁, hvy5]
    exact h.code_vec (n := 5) (by norm_num)
  have key_v₂ : zjCode y z v₁ v₂ (t * v₂ * t⁻¹) = 11 := by
    rw [h.t_v₂, hvz11]
    exact h.code_vec (n := 11) (by norm_num)
  unfold zjMat
  rw [key_y, key_z, key_v₁, key_v₂, ZJFin.T]
  decide

theorem mat_l : zjMat y z v₁ v₂ l = ZJFin.L := by
  have hyz3 : y * z = zjVec y z v₁ v₂ 3 := by
    have hx := h.vec_xor (n := 1) (m := 2) (by norm_num) (by norm_num)
    rw [show (1 : ℕ) ^^^ 2 = 3 by decide] at hx
    calc y * z = zjVec y z v₁ v₂ 1 * zjVec y z v₁ v₂ 2 := by
          rw [(h.vec_basis).2.1, (h.vec_basis).2.2.1]
      _ = zjVec y z v₁ v₂ 3 := hx.symm
  have hvy5 : v₁ * y = zjVec y z v₁ v₂ 5 := by
    have hx := h.vec_xor (n := 4) (m := 1) (by norm_num) (by norm_num)
    rw [show (4 : ℕ) ^^^ 1 = 5 by decide] at hx
    calc v₁ * y = zjVec y z v₁ v₂ 4 * zjVec y z v₁ v₂ 1 := by
          rw [(h.vec_basis).2.2.2.1, (h.vec_basis).2.1]
      _ = zjVec y z v₁ v₂ 5 := hx.symm
  have hvz11 : v₂ * (y * z) = zjVec y z v₁ v₂ 11 := by
    have hx := h.vec_xor (n := 8) (m := 3) (by norm_num) (by norm_num)
    rw [show (8 : ℕ) ^^^ 3 = 11 by decide] at hx
    calc v₂ * (y * z) = zjVec y z v₁ v₂ 8 * zjVec y z v₁ v₂ 3 := by
          rw [(h.vec_basis).2.2.2.2, hyz3]
      _ = zjVec y z v₁ v₂ 11 := hx.symm
  have key_y : zjCode y z v₁ v₂ (l * y * l⁻¹) = 3 := by
    rw [h.l_y, hyz3]
    exact h.code_vec (n := 3) (by norm_num)
  have key_z : zjCode y z v₁ v₂ (l * z * l⁻¹) = 2 := by
    rw [h.l_z]
    exact (by simpa [(h.vec_basis).2.2.1] using h.code_vec (n := 2) (by norm_num))
  have ha_yz : (l * v₁ * l⁻¹) * (y * z) = v₂ := by
    have hstep : (l * t) * v₁ * (l * t)⁻¹ = (l * v₁ * l⁻¹) * (y * z) := by
      rw [show (l * t) * v₁ * (l * t)⁻¹ = l * (t * v₁ * t⁻¹) * l⁻¹ by group, h.t_v₁]
      rw [show l * (v₁ * y) * l⁻¹ = (l * v₁ * l⁻¹) * (l * y * l⁻¹) by group, h.l_y]
    rw [← hstep]
    exact h.lt_v₁
  have ha : l * v₁ * l⁻¹ = zjVec y z v₁ v₂ 11 := by
    have hyzY : y * z ∈ Y := mul_mem h.y_mem h.z_mem
    have hyz2 : (y * z) * (y * z) = 1 := h.Y_sq (y * z) hyzY
    have hfin : l * v₁ * l⁻¹ = v₂ * (y * z) := by
      calc l * v₁ * l⁻¹ = (l * v₁ * l⁻¹) * ((y * z) * (y * z)) := by
            rw [hyz2]; group
        _ = ((l * v₁ * l⁻¹) * (y * z)) * (y * z) := by group
        _ = v₂ * (y * z) := by rw [ha_yz]
    rw [hfin, hvz11]
  have key_v₁ : zjCode y z v₁ v₂ (l * v₁ * l⁻¹) = 11 := by
    rw [ha]
    exact h.code_vec (n := 11) (by norm_num)
  have hlt_sq : (l * t) * (l * t) = 1 := by
    calc (l * t) * (l * t) = l * (t * l) * t := by group
      _ = l * (l * t) * t := by rw [h.t_l]
      _ = (l * l) * (t * t) := by group
      _ = 1 := by rw [h.l_sq, h.t_sq]; group
  have hconj_yz : l * (y * z) * l⁻¹ = y := by
    rw [show l * (y * z) * l⁻¹ = (l * y * l⁻¹) * (l * z * l⁻¹) by group, h.l_y, h.l_z]
    rw [show (y * z) * z = y * (z * z) by group, h.Y_sq z h.z_mem]
    group
  have hlt_v₂' : (l * t) * v₂ * (l * t)⁻¹ = (l * v₂ * l⁻¹) * y := by
    rw [show (l * t) * v₂ * (l * t)⁻¹ = l * (t * v₂ * t⁻¹) * l⁻¹ by group, h.t_v₂]
    rw [show l * (v₂ * (y * z)) * l⁻¹ = (l * v₂ * l⁻¹) * (l * (y * z) * l⁻¹) by group,
      hconj_yz]
  have hlt_v₂ : (l * t) * v₂ * (l * t)⁻¹ = v₁ := by
    rw [← h.lt_v₁]
    rw [show (l * t) * ((l * t) * v₁ * (l * t)⁻¹) * (l * t)⁻¹ =
        ((l * t) * (l * t)) * v₁ * ((l * t) * (l * t))⁻¹ by group, hlt_sq]
    group
  have hb_y : (l * v₂ * l⁻¹) * y = v₁ := by
    rw [← hlt_v₂']
    exact hlt_v₂
  have hb : l * v₂ * l⁻¹ = zjVec y z v₁ v₂ 5 := by
    have hy2 : y * y = 1 := h.Y_sq y h.y_mem
    have hfin : l * v₂ * l⁻¹ = v₁ * y := by
      calc l * v₂ * l⁻¹ = (l * v₂ * l⁻¹) * (y * y) := by rw [hy2]; group
        _ = ((l * v₂ * l⁻¹) * y) * y := by group
        _ = v₁ * y := by rw [hb_y]
    rw [hfin, hvy5]
  have key_v₂ : zjCode y z v₁ v₂ (l * v₂ * l⁻¹) = 5 := by
    rw [hb]
    exact h.code_vec (n := 5) (by norm_num)
  unfold zjMat
  rw [key_y, key_z, key_v₁, key_v₂, ZJFin.L]
  decide

theorem mat_rho : zjMat y z v₁ v₂ ρ = ZJFin.R ∨ zjMat y z v₁ v₂ ρ = ZJFin.R2 := by
  have h1 : ZJFin.mmul ZJFin.T (zjMat y z v₁ v₂ ρ) =
      ZJFin.mmul (zjMat y z v₁ v₂ ρ) ZJFin.T := by
    calc ZJFin.mmul ZJFin.T (zjMat y z v₁ v₂ ρ)
        = ZJFin.mmul (zjMat y z v₁ v₂ t) (zjMat y z v₁ v₂ ρ) := by rw [h.mat_t]
      _ = zjMat y z v₁ v₂ (t * ρ) := (h.mat_mul t ρ).symm
      _ = zjMat y z v₁ v₂ (ρ * t) := by rw [h.t_rho]
      _ = ZJFin.mmul (zjMat y z v₁ v₂ ρ) (zjMat y z v₁ v₂ t) := h.mat_mul ρ t
      _ = ZJFin.mmul (zjMat y z v₁ v₂ ρ) ZJFin.T := by rw [h.mat_t]
  have hρ3 : ρ * (ρ * ρ) = 1 := by simpa [pow_three] using h.rho_pow_three
  have h3 : ZJFin.mmul (zjMat y z v₁ v₂ ρ)
      (ZJFin.mmul (zjMat y z v₁ v₂ ρ) (zjMat y z v₁ v₂ ρ)) = ZJFin.one := by
    calc ZJFin.mmul (zjMat y z v₁ v₂ ρ)
          (ZJFin.mmul (zjMat y z v₁ v₂ ρ) (zjMat y z v₁ v₂ ρ))
        = ZJFin.mmul (zjMat y z v₁ v₂ ρ) (zjMat y z v₁ v₂ (ρ * ρ)) := by
            rw [h.mat_mul ρ ρ]
      _ = zjMat y z v₁ v₂ (ρ * (ρ * ρ)) := (h.mat_mul ρ (ρ * ρ)).symm
      _ = zjMat y z v₁ v₂ 1 := by rw [hρ3]
      _ = ZJFin.one := h.mat_one
  have hρinv : ρ⁻¹ = ρ * ρ := inv_eq_of_mul_eq_one_right hρ3
  have hlr : l * ρ = (ρ * ρ) * l := by
    rw [show l * ρ = (l * ρ * l⁻¹) * l by group, h.l_rho, hρinv]
  have h4 : ZJFin.mmul ZJFin.L (zjMat y z v₁ v₂ ρ) =
      ZJFin.mmul (ZJFin.mmul (zjMat y z v₁ v₂ ρ) (zjMat y z v₁ v₂ ρ)) ZJFin.L := by
    calc ZJFin.mmul ZJFin.L (zjMat y z v₁ v₂ ρ)
        = ZJFin.mmul (zjMat y z v₁ v₂ l) (zjMat y z v₁ v₂ ρ) := by rw [h.mat_l]
      _ = zjMat y z v₁ v₂ (l * ρ) := (h.mat_mul l ρ).symm
      _ = zjMat y z v₁ v₂ ((ρ * ρ) * l) := by rw [hlr]
      _ = ZJFin.mmul (zjMat y z v₁ v₂ (ρ * ρ)) (zjMat y z v₁ v₂ l) := h.mat_mul (ρ * ρ) l
      _ = ZJFin.mmul (ZJFin.mmul (zjMat y z v₁ v₂ ρ) (zjMat y z v₁ v₂ ρ)) ZJFin.L := by
            rw [h.mat_mul ρ ρ, h.mat_l]
  have h5 : ∀ n ∈ List.range 16, n ≠ 0 → ZJFin.app (zjMat y z v₁ v₂ ρ) n ≠ n := by
    intro n hn hn0 happ
    have hn16 : n < 16 := List.mem_range.mp hn
    have hcode : zjCode y z v₁ v₂ (ρ * zjVec y z v₁ v₂ n * ρ⁻¹) = n := by
      rw [← h.mat_app (n := n) hn16 ρ]
      exact happ
    have hcode' : zjCode y z v₁ v₂ (zjVec y z v₁ v₂ n) = n := h.code_vec hn16
    have hmem1 : ρ * zjVec y z v₁ v₂ n * ρ⁻¹ ∈ Y := h.rho_norm_Y _ (h.vec_mem n)
    have hmem2 : zjVec y z v₁ v₂ n ∈ Y := h.vec_mem n
    have heq : ρ * zjVec y z v₁ v₂ n * ρ⁻¹ = zjVec y z v₁ v₂ n :=
      h.eq_of_code_eq hmem1 hmem2 (by rw [hcode, hcode'])
    have hq : zjVec y z v₁ v₂ n ∈ Q := h.Y_le_Q hmem2
    exact hn0 (h.vec_eq_one hn16 (h.rho_fpf_Q _ hq heq))
  have h6 : ∀ n ∈ [4, 8, 12], ZJFin.app (zjMat y z v₁ v₂ ρ) n &&& 3 = 0 := by
    intro n hn
    have hnmem : n = 4 ∨ n = 8 ∨ n = 12 := by simpa using hn
    rcases hnmem with rfl | rfl | rfl
    · rw [h.mat_app (n := 4) (by norm_num) ρ]
      exact (h.code_and_three_iff (h.rho_norm_Y _ (h.vec_mem 4))).2
        (h.rho_norm_V' _ (by
          rw [h.V'_eq, (h.vec_basis).2.2.2.1]
          exact Subgroup.subset_closure (by simp)))
    · rw [h.mat_app (n := 8) (by norm_num) ρ]
      exact (h.code_and_three_iff (h.rho_norm_Y _ (h.vec_mem 8))).2
        (h.rho_norm_V' _ (by
          rw [h.V'_eq, (h.vec_basis).2.2.2.2]
          exact Subgroup.subset_closure (by simp)))
    · rw [h.mat_app (n := 12) (by norm_num) ρ]
      exact (h.code_and_three_iff (h.rho_norm_Y _ (h.vec_mem 12))).2
        (h.rho_norm_V' _ (by
          have hx := h.vec_xor (n := 4) (m := 8) (by norm_num) (by norm_num)
          rw [show (4 : ℕ) ^^^ 8 = 12 by decide] at hx
          rw [hx, (h.vec_basis).2.2.2.1, (h.vec_basis).2.2.2.2]
          exact mul_mem
            (by rw [h.V'_eq]; exact Subgroup.subset_closure (by simp))
            (by rw [h.V'_eq]; exact Subgroup.subset_closure (by simp))))
  rcases ZJFin.rho_cases (zjMat y z v₁ v₂ ρ) (h.mat_mem_P ρ) h1 h3 h4 h5 h6 with hR | hR2
  · exact Or.inl hR
  · exact Or.inr hR2

end ZJBase

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
