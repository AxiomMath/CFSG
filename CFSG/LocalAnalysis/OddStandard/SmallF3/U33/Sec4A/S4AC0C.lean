module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.CtxData

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

theorem y_mul_self_ne_one (h : WreathRel x₁ x₂ lam) : x₁ ^ 2 * x₁ ^ 2 = 1 ∧ x₁ ^ 2 ≠ 1 := by
  have hx₁4 : x₁ ^ 4 = 1 := by
    rw [← h.ord_x₁]
    exact pow_orderOf_eq_one x₁
  constructor
  · rw [← pow_add, show (2 + 2 : ℕ) = 4 from rfl, hx₁4]
  · intro h1
    have hdvd : orderOf x₁ ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr h1
    rw [h.ord_x₁] at hdvd
    norm_num at hdvd

theorem yz_mul_self_ne_one (h : WreathRel x₁ x₂ lam) :
    (x₁ ^ 2 * (x₁ * x₂) ^ 2) * (x₁ ^ 2 * (x₁ * x₂) ^ 2) = 1 ∧
      x₁ ^ 2 * (x₁ * x₂) ^ 2 ≠ 1 := by
  have hcomm : Commute x₁ x₂ := h.comm
  have hx₁4 : x₁ ^ 4 = 1 := by
    rw [← h.ord_x₁]
    exact pow_orderOf_eq_one x₁
  have hx₂4 : x₂ ^ 4 = 1 := by
    rw [← h.ord_x₂]
    exact pow_orderOf_eq_one x₂
  have hz : (x₁ * x₂) ^ 2 = x₁ ^ 2 * x₂ ^ 2 := hcomm.mul_pow 2
  have hyz : x₁ ^ 2 * (x₁ * x₂) ^ 2 = x₂ ^ 2 := by
    rw [hz, ← mul_assoc, ← pow_add, show (2 + 2 : ℕ) = 4 from rfl, hx₁4, one_mul]
  constructor
  · rw [hyz, ← pow_add, show (2 + 2 : ℕ) = 4 from rfl, hx₂4]
  · intro h1
    have hx₂sq : x₂ ^ 2 = 1 := by
      rw [← hyz]
      exact h1
    have hdvd : orderOf x₂ ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hx₂sq
    rw [h.ord_x₂] at hdvd
    norm_num at hdvd

theorem y_commute_z (h : WreathRel x₁ x₂ lam) :
    x₁ ^ 2 * (x₁ * x₂) ^ 2 = (x₁ * x₂) ^ 2 * x₁ ^ 2 := by
  have hcomm : Commute x₁ x₂ := h.comm
  exact (((Commute.refl x₁).mul_right hcomm).pow_left 2).pow_right 2 |>.eq

theorem tau_commute_y (h : Ctx t L S x₁ x₂ lam rho tau) : tau * x₁ ^ 2 = x₁ ^ 2 * tau := by
  have hsq : x₁ ^ 2 * x₁ ^ 2 = 1 := (y_mul_self_ne_one h.wreath).1
  have hconj : tau * x₁ ^ 2 * tau⁻¹ = x₁ ^ 2 := by
    rw [← conj_pow (a := tau) (b := x₁) (i := 2), h.tau_x₁, inv_pow,
      inv_eq_of_mul_eq_one_right hsq]
  exact mul_inv_eq_iff_eq_mul.mp hconj

theorem tau_commute_z (h : Ctx t L S x₁ x₂ lam rho tau) :
    tau * (x₁ * x₂) ^ 2 = (x₁ * x₂) ^ 2 * tau := by
  have hcomm : Commute x₁ x₂ := h.wreath.comm
  have hsq : (x₁ * x₂) ^ 2 * (x₁ * x₂) ^ 2 = 1 := h.wreath.sq_x₁x₂_mul_self
  have h1 : tau * (x₁ * x₂) * tau⁻¹ = (x₁ * x₂)⁻¹ := by
    calc tau * (x₁ * x₂) * tau⁻¹
        = (tau * x₁ * tau⁻¹) * (tau * x₂ * tau⁻¹) := by group
      _ = x₁⁻¹ * x₂⁻¹ := by rw [h.tau_x₁, h.tau_x₂]
      _ = (x₂ * x₁)⁻¹ := by rw [mul_inv_rev]
      _ = (x₁ * x₂)⁻¹ := by rw [← hcomm.eq]
  have hconj : tau * (x₁ * x₂) ^ 2 * tau⁻¹ = (x₁ * x₂) ^ 2 := by
    rw [← conj_pow (a := tau) (b := x₁ * x₂) (i := 2), h1, inv_pow,
      inv_eq_of_mul_eq_one_right hsq]
  exact mul_inv_eq_iff_eq_mul.mp hconj

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
