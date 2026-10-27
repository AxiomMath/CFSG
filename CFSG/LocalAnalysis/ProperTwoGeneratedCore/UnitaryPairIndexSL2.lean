module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.ProperTwoGeneratedCore.UnitaryPairIndex.SL2

open Matrix

variable {F : Type*} [Field F]

@[expose] def unipotentOne : SpecialLinearGroup (Fin 2) F :=
  ⟨!![1, 1; 0, 1], by simp [det_fin_two]⟩

theorem coe_unipotentOne :
    ((unipotentOne : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![1, 1; 0, 1] :=
  rfl

theorem exists_conj_unipotentOne (h2 : (2 : F) = 0) (hsq : ∀ a : F, ∃ b : F, b * b = a)
    {x : SpecialLinearGroup (Fin 2) F} (hx : x * x = 1) (hx1 : x ≠ 1) :
    ∃ g : SpecialLinearGroup (Fin 2) F, g * unipotentOne * g⁻¹ = x := by
  set a := (x : Matrix (Fin 2) (Fin 2) F) 0 0 with ha
  set b := (x : Matrix (Fin 2) (Fin 2) F) 0 1 with hb
  set c := (x : Matrix (Fin 2) (Fin 2) F) 1 0 with hc
  set d := (x : Matrix (Fin 2) (Fin 2) F) 1 1 with hd
  have hxm : (x : Matrix (Fin 2) (Fin 2) F) = !![a, b; c, d] := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hdet : a * d - b * c = 1 := by
    have := x.2
    rwa [hxm, det_fin_two_of] at this
  have hsq' : (x : Matrix (Fin 2) (Fin 2) F) * (x : Matrix (Fin 2) (Fin 2) F) = 1 := by
    have := congrArg (fun y : SpecialLinearGroup (Fin 2) F => (y : Matrix (Fin 2) (Fin 2) F)) hx
    simpa using this
  rw [hxm] at hsq'
  have e00 := congrFun (congrFun hsq' 0) 0
  have e11 := congrFun (congrFun hsq' 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e11
  have had : a = d := by
    have h1 : a * (a - d) = 0 := by linear_combination e00 - hdet - b * c * h2
    have h2' : d * (d - a) = 0 := by linear_combination e11 - hdet - b * c * h2
    by_contra hne
    have hsub : a - d ≠ 0 := sub_ne_zero.mpr hne
    have ha0 : a = 0 := (mul_eq_zero.mp h1).resolve_right hsub
    have hd0 : d = 0 := (mul_eq_zero.mp h2').resolve_right (by
      intro h
      exact hsub (by linear_combination -h))
    exact hne (ha0.trans hd0.symm)
  rw [← had] at hxm hdet
  have hbc : a * a + b * c = 1 := by linear_combination hdet + b * c * h2
  suffices hP : ∃ P : SpecialLinearGroup (Fin 2) F, x * P = P * unipotentOne by
    obtain ⟨P, hP⟩ := hP
    exact ⟨P, by rw [← hP, mul_inv_cancel_right]⟩
  by_cases hc0 : c = 0
  ·
    rw [hc0, mul_zero, add_zero] at hbc
    have ha1 : a = 1 := by
      have h' : (a + 1) * (a + 1) = 0 := by linear_combination hbc + (a + 1) * h2
      have := mul_self_eq_zero.mp h'
      linear_combination this - h2
    have hb0 : b ≠ 0 := by
      intro hb0
      apply hx1
      apply Subtype.ext
      rw [hxm, hc0, hb0, ha1]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    obtain ⟨e, he⟩ := hsq b
    have he0 : e ≠ 0 := by
      rintro rfl
      rw [mul_zero] at he
      exact hb0 he.symm
    set P : SpecialLinearGroup (Fin 2) F := ⟨!![e, 0; 0, e⁻¹], by simp [det_fin_two, he0]⟩
    have hP : (P : Matrix (Fin 2) (Fin 2) F) = !![e, 0; 0, e⁻¹] := rfl
    refine ⟨P, ?_⟩
    ext i j
    rw [SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_mul, hP, coe_unipotentOne, hxm, hc0,
      ha1]
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    rw [← he]
    field_simp
  ·
    obtain ⟨e, he⟩ := hsq c⁻¹
    have hdetP : (!![e * (a + 1), e; e * c, 0] : Matrix (Fin 2) (Fin 2) F).det = 1 := by
      rw [det_fin_two_of]
      have : e * e * c = 1 := by rw [he, inv_mul_cancel₀ hc0]
      linear_combination -this - h2
    set P : SpecialLinearGroup (Fin 2) F := ⟨!![e * (a + 1), e; e * c, 0], hdetP⟩
    have hP : (P : Matrix (Fin 2) (Fin 2) F) = !![e * (a + 1), e; e * c, 0] := rfl
    refine ⟨P, ?_⟩
    ext i j
    rw [SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_mul, hP, coe_unipotentOne, hxm]
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    · linear_combination e * hbc
    · linear_combination -e * h2
    · linear_combination a * e * c * h2
    · ring

theorem sl2_involutions_conj (h2 : (2 : F) = 0) (hsq : ∀ a : F, ∃ b : F, b * b = a)
    {x y : SpecialLinearGroup (Fin 2) F} (hx : x * x = 1) (hx1 : x ≠ 1) (hy : y * y = 1)
    (hy1 : y ≠ 1) : ∃ g : SpecialLinearGroup (Fin 2) F, g⁻¹ * x * g = y := by
  obtain ⟨g, hg⟩ := exists_conj_unipotentOne h2 hsq hx hx1
  obtain ⟨k, hk⟩ := exists_conj_unipotentOne h2 hsq hy hy1
  refine ⟨g * k⁻¹, ?_⟩
  rw [← hg, ← hk]
  group

end CFSG.ProperTwoGeneratedCore.UnitaryPairIndex.SL2
