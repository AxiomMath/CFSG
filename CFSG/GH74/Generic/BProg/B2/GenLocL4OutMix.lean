module

public import CFSG.LinearAlgebra.LinearGroups.Generation

public section

namespace CFSG.GH74.Generic.BProg.B2.GenLocL4Out

open CFSG Matrix
open scoped MatrixGroups


section Mix

variable {F : Type} [Field F]

@[expose] def tv (i j : Fin 4) (h : i ≠ j) (a : F) : SL(4, F) := Matrix.SpecialLinearGroup.transvection h a

theorem coe_tv (i j : Fin 4) (h : i ≠ j) (a : F) :
    ((tv i j h a : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) = 1 + Matrix.single i j a :=
  CFSG.LinearGroups.coe_transvection h a

theorem tv_mul (i j : Fin 4) (h : i ≠ j) (a b : F) : tv i j h a * tv i j h b = tv i j h (a + b) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_tv, coe_tv, coe_tv]
  ext p q
  fin_cases p <;> fin_cases q <;> fin_cases i <;> fin_cases j <;> simp_all [Matrix.mul_apply, Matrix.single_apply, Fin.sum_univ_four] <;> ring

@[expose] def rot02 (m y z : F) (h : m * m - y * z = 1) : SL(4, F) :=
  ⟨!![m, 0, y, 0; 0, 1, 0, 0; z, 0, m, 0; 0, 0, 0, 1], by
    simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]; linear_combination h⟩

@[expose] def rot13 (m y z : F) (h : m * m - y * z = 1) : SL(4, F) :=
  ⟨!![1, 0, 0, 0; 0, m, 0, y; 0, 0, 1, 0; 0, z, 0, m], by
    simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]; linear_combination h⟩

theorem coe_rot02 (m y z : F) (h : m * m - y * z = 1) :
    ((rot02 m y z h : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) = !![m, 0, y, 0; 0, 1, 0, 0; z, 0, m, 0; 0, 0, 0, 1] := rfl

theorem coe_rot13 (m y z : F) (h : m * m - y * z = 1) :
    ((rot13 m y z h : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) = !![1, 0, 0, 0; 0, m, 0, y; 0, 0, 1, 0; 0, z, 0, m] := rfl

@[expose] def wH : SL(4, F) := ⟨!![0, -1, 0, 0; 1, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1], by
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]⟩

theorem coe_wH : ((wH : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) = !![0, -1, 0, 0; 1, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] := rfl

theorem rot02_tv01 (m y z : F) (h : m * m - y * z = 1) (s : F) :
    rot02 m y z h * tv 0 1 (by decide) s = (tv 0 1 (by decide) (s * m) * tv 2 1 (by decide) (s * z)) * rot02 m y z h := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_tv, coe_rot02]
  ext p q
  fin_cases p <;> fin_cases q <;> simp [Matrix.mul_apply, Matrix.single_apply, Fin.sum_univ_four] <;> ring

theorem rot02_tv10 (m y z : F) (h : m * m - y * z = 1) (s : F) :
    rot02 m y z h * tv 1 0 (by decide) s = (tv 1 0 (by decide) (s * m) * tv 1 2 (by decide) (-(s * y))) * rot02 m y z h := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_tv, coe_rot02]
  ext p q
  fin_cases p <;> fin_cases q <;> simp [Matrix.mul_apply, Matrix.single_apply, Fin.sum_univ_four]
  all_goals first | ring1 | linear_combination (-s) * h

theorem rot13_tv10 (m y z : F) (h : m * m - y * z = 1) (s : F) :
    rot13 m y z h * tv 1 0 (by decide) s = (tv 1 0 (by decide) (s * m) * tv 3 0 (by decide) (s * z)) * rot13 m y z h := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_tv, coe_rot13]
  ext p q
  fin_cases p <;> fin_cases q <;> simp [Matrix.mul_apply, Matrix.single_apply, Fin.sum_univ_four]
  all_goals first | ring1 | linear_combination (-s) * h

theorem rot13_tv01 (m y z : F) (h : m * m - y * z = 1) (s : F) :
    rot13 m y z h * tv 0 1 (by decide) s = (tv 0 1 (by decide) (s * m) * tv 0 3 (by decide) (-(s * y))) * rot13 m y z h := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_tv, coe_rot13]
  ext p q
  fin_cases p <;> fin_cases q <;> simp [Matrix.mul_apply, Matrix.single_apply, Fin.sum_univ_four]
  all_goals first | ring1 | linear_combination (-s) * h

theorem wH_tv21 (a : F) : wH * tv 2 1 (by decide) a = tv 2 0 (by decide) (-a) * wH := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_tv, coe_wH]
  ext p q
  fin_cases p <;> fin_cases q <;> simp [Matrix.mul_apply, Matrix.single_apply, Fin.sum_univ_four]

theorem wH_tv12 (a : F) : wH * tv 1 2 (by decide) a = tv 0 2 (by decide) (-a) * wH := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_tv, coe_wH]
  ext p q
  fin_cases p <;> fin_cases q <;> simp [Matrix.mul_apply, Matrix.single_apply, Fin.sum_univ_four]

theorem wH_tv30 (a : F) : wH * tv 3 0 (by decide) a = tv 3 1 (by decide) a * wH := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_tv, coe_wH]
  ext p q
  fin_cases p <;> fin_cases q <;> simp [Matrix.mul_apply, Matrix.single_apply, Fin.sum_univ_four]

theorem wH_tv03 (a : F) : wH * tv 0 3 (by decide) a = tv 1 3 (by decide) a * wH := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_tv, coe_wH]
  ext p q
  fin_cases p <;> fin_cases q <;> simp [Matrix.mul_apply, Matrix.single_apply, Fin.sum_univ_four]

theorem comm20_03 (a b : F) : tv 2 0 (by decide) a * tv 0 3 (by decide) b =
    tv 2 3 (by decide) (a * b) * (tv 0 3 (by decide) b * tv 2 0 (by decide) a) := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_tv]
  ext p q
  fin_cases p <;> fin_cases q <;> simp [Matrix.mul_apply, Matrix.single_apply, Fin.sum_univ_four] <;> ring

theorem comm30_02 (a b : F) : tv 3 0 (by decide) a * tv 0 2 (by decide) b =
    tv 3 2 (by decide) (a * b) * (tv 0 2 (by decide) b * tv 3 0 (by decide) a) := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_tv]
  ext p q
  fin_cases p <;> fin_cases q <;> simp [Matrix.mul_apply, Matrix.single_apply, Fin.sum_univ_four] <;> ring

theorem wH_eq : (wH : SL(4, F)) = tv 0 1 (by decide) (-1) * tv 1 0 (by decide) 1 * tv 0 1 (by decide) (-1) := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_tv, coe_wH]
  ext p q
  fin_cases p <;> fin_cases q <;> simp [Matrix.mul_apply, Matrix.single_apply, Fin.sum_univ_four]

theorem mem_of_conj_eq {Γ : Subgroup SL(4, F)} {r x q : SL(4, F)} (hr : r ∈ Γ) (hx : x ∈ Γ) (h : r * x = q * r) :
    q ∈ Γ := by
  have : q = r * x * r⁻¹ := by rw [h]; group
  rw [this]
  exact Γ.mul_mem (Γ.mul_mem hr hx) (Γ.inv_mem hr)

theorem mem_of_conj_eq' {Γ : Subgroup SL(4, F)} {r x p q : SL(4, F)} (hr : r ∈ Γ) (hx : x ∈ Γ) (hp : p ∈ Γ)
    (h : r * x = (p * q) * r) : q ∈ Γ := by
  have : q = p⁻¹ * (r * x * r⁻¹) := by rw [h]; group
  rw [this]
  exact Γ.mul_mem (Γ.inv_mem hp) (Γ.mul_mem (Γ.mul_mem hr hx) (Γ.inv_mem hr))

theorem mix_top (Γ : Subgroup SL(4, F)) (h01 : ∀ a, tv 0 1 (by decide) a ∈ Γ) (h10 : ∀ a, tv 1 0 (by decide) a ∈ Γ)
    (m y z : F) (h : m * m - y * z = 1) (hy : y ≠ 0) (hz : z ≠ 0) (hr1 : rot02 m y z h ∈ Γ)
    (m' y' z' : F) (h' : m' * m' - y' * z' = 1) (hy' : y' ≠ 0) (hz' : z' ≠ 0) (hr2 : rot13 m' y' z' h' ∈ Γ) :
    Γ = ⊤ := by
  have hw : (wH : SL(4, F)) ∈ Γ := by
    rw [wH_eq]; exact Γ.mul_mem (Γ.mul_mem (h01 _) (h10 _)) (h01 _)
  have t21 : ∀ a, tv 2 1 (by decide) a ∈ Γ := fun a => by
    have := mem_of_conj_eq' (Γ := Γ) hr1 (h01 (a / z)) (h01 ((a / z) * m)) (rot02_tv01 m y z h (a / z))
    rwa [show a / z * z = a by field_simp] at this
  have t12 : ∀ a, tv 1 2 (by decide) a ∈ Γ := fun a => by
    have := mem_of_conj_eq' (Γ := Γ) hr1 (h10 (-a / y)) (h10 ((-a / y) * m)) (rot02_tv10 m y z h (-a / y))
    rwa [show -(-a / y * y) = a by field_simp] at this
  have t20 : ∀ a, tv 2 0 (by decide) a ∈ Γ := fun a => by
    have := mem_of_conj_eq (Γ := Γ) hw (t21 (-a)) (wH_tv21 (-a))
    rwa [neg_neg] at this
  have t02 : ∀ a, tv 0 2 (by decide) a ∈ Γ := fun a => by
    have := mem_of_conj_eq (Γ := Γ) hw (t12 (-a)) (wH_tv12 (-a))
    rwa [neg_neg] at this
  have t30 : ∀ a, tv 3 0 (by decide) a ∈ Γ := fun a => by
    have := mem_of_conj_eq' (Γ := Γ) hr2 (h10 (a / z')) (h10 ((a / z') * m')) (rot13_tv10 m' y' z' h' (a / z'))
    rwa [show a / z' * z' = a by field_simp] at this
  have t03 : ∀ a, tv 0 3 (by decide) a ∈ Γ := fun a => by
    have := mem_of_conj_eq' (Γ := Γ) hr2 (h01 (-a / y')) (h01 ((-a / y') * m')) (rot13_tv01 m' y' z' h' (-a / y'))
    rwa [show -(-a / y' * y') = a by field_simp] at this
  have t31 : ∀ a, tv 3 1 (by decide) a ∈ Γ := fun a => mem_of_conj_eq (Γ := Γ) hw (t30 a) (wH_tv30 a)
  have t13 : ∀ a, tv 1 3 (by decide) a ∈ Γ := fun a => mem_of_conj_eq (Γ := Γ) hw (t03 a) (wH_tv03 a)
  have t23 : ∀ a, tv 2 3 (by decide) a ∈ Γ := fun a => by
    have h1 := comm20_03 a 1
    rw [mul_one] at h1
    have : tv 2 3 (by decide) a = tv 2 0 (by decide) a * tv 0 3 (by decide) 1 * (tv 0 3 (by decide) 1 * tv 2 0 (by decide) a)⁻¹ := by
      rw [h1]; group
    rw [this]
    exact Γ.mul_mem (Γ.mul_mem (t20 a) (t03 1)) (Γ.inv_mem (Γ.mul_mem (t03 1) (t20 a)))
  have t32 : ∀ a, tv 3 2 (by decide) a ∈ Γ := fun a => by
    have h1 := comm30_02 a 1
    rw [mul_one] at h1
    have : tv 3 2 (by decide) a = tv 3 0 (by decide) a * tv 0 2 (by decide) 1 * (tv 0 2 (by decide) 1 * tv 3 0 (by decide) a)⁻¹ := by
      rw [h1]; group
    rw [this]
    exact Γ.mul_mem (Γ.mul_mem (t30 a) (t02 1)) (Γ.inv_mem (Γ.mul_mem (t02 1) (t30 a)))
  rw [eq_top_iff, ← CFSG.LinearGroups.special_linear_elementary_generation (n := 4) (K := F)]
  refine (Subgroup.closure_le Γ).2 ?_
  rintro _ ⟨i, j, hij, c, rfl⟩
  fin_cases i <;> fin_cases j
  all_goals first
    | exact absurd rfl hij
    | exact h01 c | exact h10 c | exact t21 c | exact t12 c | exact t20 c | exact t02 c
    | exact t30 c | exact t03 c | exact t31 c | exact t13 c | exact t23 c | exact t32 c

end Mix


end CFSG.GH74.Generic.BProg.B2.GenLocL4Out
