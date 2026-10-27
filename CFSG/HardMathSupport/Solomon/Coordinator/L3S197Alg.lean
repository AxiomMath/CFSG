module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open Polynomial

theorem aeval_cubic {F : Type*} [Field F] {p : F[X]} (hm : p.Monic) (h3 : p.natDegree = 3)
    (M : Matrix (Fin 3) (Fin 3) F) :
    aeval M p = p.coeff 0 • (1 : Matrix (Fin 3) (Fin 3) F) + p.coeff 1 • M + p.coeff 2 • M ^ 2 +
      M ^ 3 := by
  rw [aeval_eq_sum_range, h3, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_one]
  have : p.coeff 3 = 1 := by
    have := hm.coeff_natDegree
    rwa [h3] at this
  rw [this]
  simp [add_assoc]

theorem cube_eq_one_of_conj_smul {F : Type*} [Field F] {x : Matrix (Fin 3) (Fin 3) F}
    (g : GL (Fin 3) F) {c : F} (hc : c ≠ 1) (hc3 : c ^ 3 = 1)
    (hconj : (g : Matrix (Fin 3) (Fin 3) F) * x * (g : Matrix (Fin 3) (Fin 3) F)⁻¹ = c • x)
    (hdet : x.det = 1) : x ^ 3 = 1 := by
  set p := x.charpoly with hp
  have hmon : p.Monic := Matrix.charpoly_monic x
  have hdeg : p.natDegree = 3 := by
    rw [hp, Matrix.charpoly_natDegree_eq_dim]
    simp
  have hc2 : c ^ 2 + c + 1 = 0 := by
    have h1 : (c - 1) * (c ^ 2 + c + 1) = 0 := by
      have : (c - 1) * (c ^ 2 + c + 1) = c ^ 3 - 1 := by ring
      rw [this, hc3, sub_self]
    rcases mul_eq_zero.1 h1 with h | h
    · exact absurd (sub_eq_zero.1 h) hc
    · exact h
  have hconj' : (g : Matrix (Fin 3) (Fin 3) F) * (c • x) * (g : Matrix (Fin 3) (Fin 3) F)⁻¹ =
      (c ^ 2) • x := by
    rw [Matrix.mul_smul, Matrix.smul_mul, hconj, smul_smul, pow_two]
  have hp1 : (c • x).charpoly = p := by
    rw [← hconj]
    exact Matrix.charpoly_units_conj g x
  have hp2 : (c ^ 2 • x).charpoly = p := by
    rw [← hconj', Matrix.charpoly_units_conj g (c • x), hp1]
  have e0 : aeval x p = 0 := Matrix.aeval_self_charpoly x
  have e1 : aeval (c • x) p = 0 := by
    have := Matrix.aeval_self_charpoly (c • x)
    rwa [hp1] at this
  have e2 : aeval (c ^ 2 • x) p = 0 := by
    have := Matrix.aeval_self_charpoly (c ^ 2 • x)
    rwa [hp2] at this
  rw [aeval_cubic hmon hdeg] at e0 e1 e2
  set a := p.coeff 2
  set b := p.coeff 1
  set d := p.coeff 0
  have hc4 : c ^ 4 = c := by
    have : c ^ 4 = c ^ 3 * c := by ring
    rw [this, hc3, one_mul]
  have hc22 : (c ^ 2) ^ 2 = c := by
    calc (c ^ 2) ^ 2 = c ^ 4 := by ring
      _ = c := hc4
  have hc23 : (c ^ 2) ^ 3 = 1 := by
    have : (c ^ 2) ^ 3 = (c ^ 3) ^ 2 := by ring
    rw [this, hc3, one_pow]
  rw [smul_pow, smul_pow, hc3, one_smul] at e1
  rw [smul_pow, smul_pow, hc22, hc23, one_smul] at e2
  have hA1 : (b * (1 - c)) • x + (a * (1 - c ^ 2)) • x ^ 2 = 0 := by
    linear_combination (norm := module) e0 - e1
  have hA2 : (b * (1 - c ^ 2)) • x + (a * (1 - c)) • x ^ 2 = 0 := by
    linear_combination (norm := module) e0 - e2
  have h3ne : (3 : F) ≠ 0 := by
    intro h3
    apply hc
    have : (c - 1) ^ 2 = 0 := by linear_combination hc2 - c * h3
    exact sub_eq_zero.1 (pow_eq_zero_iff (two_ne_zero) |>.1 this)
  have hΔ : ((1 - c) ^ 2 - (1 - c ^ 2) ^ 2 : F) ≠ 0 := by
    intro hΔ
    have h9 : (3 : F) ^ 2 = 0 := by
      linear_combination (1 + 2 * c) * hΔ + (12 - (1 + 2 * c) * (-c ^ 2 + c + 3)) * hc2
    exact h3ne (pow_eq_zero_iff (two_ne_zero) |>.1 h9)
  have hbx : (b * ((1 - c) ^ 2 - (1 - c ^ 2) ^ 2)) • x = 0 := by
    linear_combination (norm := module) (1 - c) • hA1 - (1 - c ^ 2) • hA2
  have hxu : IsUnit x := by
    rw [Matrix.isUnit_iff_isUnit_det, hdet]
    exact isUnit_one
  have hb : b = 0 := by
    by_contra hb0
    have hs : b * ((1 - c) ^ 2 - (1 - c ^ 2) ^ 2) ≠ 0 := mul_ne_zero hb0 hΔ
    have := congrArg (fun m => (b * ((1 - c) ^ 2 - (1 - c ^ 2) ^ 2))⁻¹ • m) hbx
    simp only [smul_smul, inv_mul_cancel₀ hs, one_smul, smul_zero] at this
    rw [this] at hxu
    exact not_isUnit_zero hxu
  have hax : (a * ((1 - c) ^ 2 - (1 - c ^ 2) ^ 2)) • x ^ 2 = 0 := by
    rw [hb] at hA1 hA2
    linear_combination (norm := module) (1 - c) • hA2 - (1 - c ^ 2) • hA1
  have ha : a = 0 := by
    by_contra ha0
    have hs : a * ((1 - c) ^ 2 - (1 - c ^ 2) ^ 2) ≠ 0 := mul_ne_zero ha0 hΔ
    have := congrArg (fun m => (a * ((1 - c) ^ 2 - (1 - c ^ 2) ^ 2))⁻¹ • m) hax
    simp only [smul_smul, inv_mul_cancel₀ hs, one_smul, smul_zero] at this
    have hxu2 : IsUnit (x ^ 2) := hxu.pow 2
    rw [this] at hxu2
    exact not_isUnit_zero hxu2
  have hd : d = -1 := by
    have h1 := Matrix.det_eq_sign_charpoly_coeff x
    rw [hdet] at h1
    simp only [Fintype.card_fin] at h1
    have : d = p.coeff 0 := rfl
    rw [this, ← hp] at *
    have h2 : (-1 : F) ^ 3 * p.coeff 0 = 1 := h1.symm
    linear_combination (-1 : F) * h2
  rw [hb, ha, hd] at e0
  have : x ^ 3 = 1 := by
    linear_combination (norm := module) e0
  exact this

end CFSG.HardMathSupport.Solomon.Coordinator
