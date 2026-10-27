module

public import CFSG.GH74.GLS.Stage4.T2SL2B
public import Mathlib.Algebra.Order.Ring.Star

public section

namespace CFSG.GH74.GLS.Stage4.Rest.ZA

open CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.GLS.Stage4.Rest.T2

variable {F : Type} [Field F]

theorem two_ne_zero_of_card_odd [Finite F] (hF : Odd (Nat.card F)) : (2 : F) ≠ 0 := by
  have := Fintype.ofFinite F
  apply Ring.two_ne_zero
  intro hchar
  have h1 := (FiniteField.even_card_iff_char_two).1 hchar
  rw [← Nat.card_eq_fintype_card] at h1
  obtain ⟨k, hk⟩ := hF
  omega

theorem coe_sq_of_sq_negOne {x : SL2 F} (hx : x * x = negOne F) :
    (x : Matrix (Fin 2) (Fin 2) F) * (x : Matrix (Fin 2) (Fin 2) F) = -1 := by
  have h := congrArg (fun y : SL2 F => (y : Matrix (Fin 2) (Fin 2) F)) hx
  simp only [Matrix.SpecialLinearGroup.coe_mul] at h
  rw [t2B_negOne_eq] at h
  exact h

theorem entries_of_sq_negOne (h2 : (2 : F) ≠ 0) {x : SL2 F} (hx : x * x = negOne F) :
    (x : Matrix (Fin 2) (Fin 2) F) 1 1 = -(x : Matrix (Fin 2) (Fin 2) F) 0 0 ∧
      (x : Matrix (Fin 2) (Fin 2) F) 0 0 * (x : Matrix (Fin 2) (Fin 2) F) 0 0 +
        (x : Matrix (Fin 2) (Fin 2) F) 0 1 * (x : Matrix (Fin 2) (Fin 2) F) 1 0 = -1 := by
  have hm := coe_sq_of_sq_negOne hx
  have e00 : (x : Matrix (Fin 2) (Fin 2) F) 0 0 * (x : Matrix (Fin 2) (Fin 2) F) 0 0 +
      (x : Matrix (Fin 2) (Fin 2) F) 0 1 * (x : Matrix (Fin 2) (Fin 2) F) 1 0 = -1 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun hm 0) 0
  have e01 : (x : Matrix (Fin 2) (Fin 2) F) 0 0 * (x : Matrix (Fin 2) (Fin 2) F) 0 1 +
      (x : Matrix (Fin 2) (Fin 2) F) 0 1 * (x : Matrix (Fin 2) (Fin 2) F) 1 1 = 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun hm 0) 1
  have e10 : (x : Matrix (Fin 2) (Fin 2) F) 1 0 * (x : Matrix (Fin 2) (Fin 2) F) 0 0 +
      (x : Matrix (Fin 2) (Fin 2) F) 1 1 * (x : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun hm 1) 0
  have e11 : (x : Matrix (Fin 2) (Fin 2) F) 1 0 * (x : Matrix (Fin 2) (Fin 2) F) 0 1 +
      (x : Matrix (Fin 2) (Fin 2) F) 1 1 * (x : Matrix (Fin 2) (Fin 2) F) 1 1 = -1 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun hm 1) 1
  have hdet : (x : Matrix (Fin 2) (Fin 2) F) 0 0 * (x : Matrix (Fin 2) (Fin 2) F) 1 1 -
      (x : Matrix (Fin 2) (Fin 2) F) 0 1 * (x : Matrix (Fin 2) (Fin 2) F) 1 0 = 1 := by
    have := x.2
    rw [Matrix.det_fin_two] at this
    exact this
  refine ⟨?_, e00⟩
  by_contra hne
  have hs : (x : Matrix (Fin 2) (Fin 2) F) 0 0 + (x : Matrix (Fin 2) (Fin 2) F) 1 1 ≠ 0 :=
    fun h => hne (by linear_combination h)
  have hb0 : (x : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 :=
    (mul_eq_zero.1 (by linear_combination e01 : (x : Matrix (Fin 2) (Fin 2) F) 0 1 *
      ((x : Matrix (Fin 2) (Fin 2) F) 0 0 + (x : Matrix (Fin 2) (Fin 2) F) 1 1) = 0)).resolve_right hs
  have had : (x : Matrix (Fin 2) (Fin 2) F) 0 0 = (x : Matrix (Fin 2) (Fin 2) F) 1 1 := by
    have h : ((x : Matrix (Fin 2) (Fin 2) F) 0 0 - (x : Matrix (Fin 2) (Fin 2) F) 1 1) *
        ((x : Matrix (Fin 2) (Fin 2) F) 0 0 + (x : Matrix (Fin 2) (Fin 2) F) 1 1) = 0 := by
      linear_combination e00 - e11
    exact sub_eq_zero.1 ((mul_eq_zero.1 h).resolve_right hs)
  apply h2
  linear_combination e00 - hdet - (x : Matrix (Fin 2) (Fin 2) F) 0 0 * had -
    2 * (x : Matrix (Fin 2) (Fin 2) F) 1 0 * hb0

theorem sl2_conj_W_of_sq_negOne [Finite F] (hF : Odd (Nat.card F)) {x : SL2 F}
    (hx : x * x = negOne F) : ∃ g : SL2 F, g * sl2W F * g⁻¹ = x := by
  have h2 := two_ne_zero_of_card_odd hF
  obtain ⟨hd, e00⟩ := entries_of_sq_negOne h2 hx
  have hm := coe_sq_of_sq_negOne hx
  have e01 : (x : Matrix (Fin 2) (Fin 2) F) 0 0 * (x : Matrix (Fin 2) (Fin 2) F) 0 1 +
      (x : Matrix (Fin 2) (Fin 2) F) 0 1 * (x : Matrix (Fin 2) (Fin 2) F) 1 1 = 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun hm 0) 1
  have e10 : (x : Matrix (Fin 2) (Fin 2) F) 1 0 * (x : Matrix (Fin 2) (Fin 2) F) 0 0 +
      (x : Matrix (Fin 2) (Fin 2) F) 1 1 * (x : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun hm 1) 0
  have e11 : (x : Matrix (Fin 2) (Fin 2) F) 1 0 * (x : Matrix (Fin 2) (Fin 2) F) 0 1 +
      (x : Matrix (Fin 2) (Fin 2) F) 1 1 * (x : Matrix (Fin 2) (Fin 2) F) 1 1 = -1 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun hm 1) 1
  generalize ha : (x : Matrix (Fin 2) (Fin 2) F) 0 0 = a at e00 e01 e10 e11 hd
  generalize hb : (x : Matrix (Fin 2) (Fin 2) F) 0 1 = b at e00 e01 e10 e11 hd
  generalize hc : (x : Matrix (Fin 2) (Fin 2) F) 1 0 = c at e00 e01 e10 e11 hd
  generalize hdd : (x : Matrix (Fin 2) (Fin 2) F) 1 1 = d at e00 e01 e10 e11 hd
  have hv : ∃ v₀ v₁ : F, c * v₀ ^ 2 - 2 * a * v₀ * v₁ - b * v₁ ^ 2 = -1 := by
    by_cases hc0 : c = 0
    · have ha0 : a ≠ 0 := by
        intro ha0
        have : (0 : F) = -1 := by rw [← e00, ha0, hc0]; ring
        exact one_ne_zero (neg_eq_zero.1 this.symm)
      refine ⟨(1 - b) / (2 * a), 1, ?_⟩
      rw [hc0]
      field_simp
      ring
    · have := Fintype.ofFinite F
      have hodd : Fintype.card F % 2 = 1 := by
        rw [← Nat.card_eq_fintype_card]
        exact Nat.odd_iff.1 hF
      obtain ⟨s, t, hst⟩ := FiniteField.exists_root_sum_quadratic
        (f := Polynomial.C c * Polynomial.X ^ 2 + Polynomial.C 1)
        (g := Polynomial.C c⁻¹ * Polynomial.X ^ 2) (by
          rw [Polynomial.degree_add_eq_left_of_degree_lt]
          · rw [Polynomial.degree_C_mul hc0, Polynomial.degree_X_pow]
            rfl
          · rw [Polynomial.degree_C_mul hc0, Polynomial.degree_X_pow,
              Polynomial.degree_C one_ne_zero]
            norm_num)
        (by
          rw [Polynomial.degree_C_mul (inv_ne_zero hc0), Polynomial.degree_X_pow]
          rfl) hodd
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
        Polynomial.eval_X] at hst
      have hu : c * c⁻¹ = 1 := mul_inv_cancel₀ hc0
      refine ⟨s + a * c⁻¹ * t, t, ?_⟩
      linear_combination hst + (2 * a * s * t + a ^ 2 * c⁻¹ * t ^ 2 + b * t ^ 2) * hu -
        (c⁻¹ * t ^ 2) * e00
  obtain ⟨v₀, v₁, hQ⟩ := hv
  let g : SL2 F := ⟨!![v₀, -(a * v₀ + b * v₁); v₁, -(c * v₀ + d * v₁)], by
    rw [Matrix.det_fin_two_of]
    rw [hd]
    linear_combination (-1 : F) * hQ⟩
  refine ⟨g, ?_⟩
  rw [mul_inv_eq_iff_eq_mul]
  have hmat : (g : Matrix (Fin 2) (Fin 2) F) * (sl2W F : Matrix (Fin 2) (Fin 2) F) =
      (x : Matrix (Fin 2) (Fin 2) F) * (g : Matrix (Fin 2) (Fin 2) F) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [g, Matrix.mul_apply, Fin.sum_univ_two, ha, hb, hc, hdd]
    · linear_combination v₀ * e00 + v₁ * e01
    · linear_combination v₀ * e10 + v₁ * e11
  exact Subtype.ext (by simpa [Matrix.SpecialLinearGroup.coe_mul] using hmat)

theorem sl2_conj_of_sq_negOne [Finite F] (hF : Odd (Nat.card F)) {x y : SL2 F}
    (hx : x * x = negOne F) (hy : y * y = negOne F) : ∃ g : SL2 F, g * y * g⁻¹ = x := by
  obtain ⟨g₁, h₁⟩ := sl2_conj_W_of_sq_negOne hF hx
  obtain ⟨g₂, h₂⟩ := sl2_conj_W_of_sq_negOne hF hy
  refine ⟨g₁ * g₂⁻¹, ?_⟩
  rw [← h₁, ← h₂]
  group

end CFSG.GH74.GLS.Stage4.Rest.ZA
