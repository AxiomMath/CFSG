module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.Algebra.CharP.CharAndCard
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87.P47PGL

open Subgroup Matrix
open scoped MatrixGroups commutatorElement

section Four

variable {F : Type} [Field F]

theorem char_two_of_card_four [Finite F] (hF : Nat.card F = 4) : (2 : F) = 0 := by
  have : Fintype F := Fintype.ofFinite F
  have hchar : CharP F 2 :=
    charP_of_card_eq_prime_pow (p := 2) (f := 2) (by rw [← Nat.card_eq_fintype_card, hF]; norm_num)
  have h2 : ((2 : ℕ) : F) = 0 := (CharP.cast_eq_zero_iff F 2 2).2 dvd_rfl
  simpa using h2

theorem cube_eq_one_of_card_four (hF : Nat.card F = 4) (c : Fˣ) : c ^ 3 = 1 := by
  have h3 : Nat.card Fˣ = 3 := by rw [Nat.card_units, hF]
  have := pow_card_eq_one' (G := Fˣ) (x := c)
  rwa [h3] at this

theorem exists_ne_zero_one_of_card_four [Finite F] (hF : Nat.card F = 4) :
    ∃ a : F, a ≠ 0 ∧ a ≠ 1 := by
  have : Fintype F := Fintype.ofFinite F
  classical
  by_contra hcon
  push Not at hcon
  have hsub : (Finset.univ : Finset F) ⊆ {0, 1} := by
    intro a _
    by_cases h0 : a = 0
    · simp [h0]
    · simp [hcon a h0]
  have h1 := Finset.card_le_card hsub
  have h2 : (Finset.univ : Finset F).card = 4 := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hF]
  have h3 : ({0, 1} : Finset F).card ≤ 2 := Finset.card_le_two
  omega

end Four

section Mat

variable {F : Type} [Field F]

@[expose] def x12 (t : F) : Matrix (Fin 3) (Fin 3) F := !![1, t, 0; 0, 1, 0; 0, 0, 1]

@[expose] def x23 (t : F) : Matrix (Fin 3) (Fin 3) F := !![1, 0, 0; 0, 1, t; 0, 0, 1]

theorem x12_mul (s t : F) : x12 s * x12 t = x12 (s + t) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [x12, Matrix.mul_apply, Fin.sum_univ_three]
  all_goals ring

theorem x23_mul (s t : F) : x23 s * x23 t = x23 (s + t) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [x23, Matrix.mul_apply, Fin.sum_univ_three]
  all_goals ring

theorem x12_zero : x12 (0 : F) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [x12]

theorem x23_zero : x23 (0 : F) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [x23]

theorem det_x12 (t : F) : (x12 t).det = 1 := by
  simp [x12, Matrix.det_fin_three]

theorem det_x23 (t : F) : (x23 t).det = 1 := by
  simp [x23, Matrix.det_fin_three]

@[expose] noncomputable def x12GL (t : F) : GL (Fin 3) F :=
  GeneralLinearGroup.mkOfDetNeZero (x12 t) (by rw [det_x12]; exact one_ne_zero)

@[expose] noncomputable def x23GL (t : F) : GL (Fin 3) F :=
  GeneralLinearGroup.mkOfDetNeZero (x23 t) (by rw [det_x23]; exact one_ne_zero)

theorem x12GL_sq (h2 : (2 : F) = 0) : x12GL (1 : F) * x12GL 1 = 1 := by
  apply Units.ext
  change x12 (1 : F) * x12 1 = 1
  rw [x12_mul, one_add_one_eq_two, h2, x12_zero]

theorem x23GL_sq (h2 : (2 : F) = 0) : x23GL (1 : F) * x23GL 1 = 1 := by
  apply Units.ext
  change x23 (1 : F) * x23 1 = 1
  rw [x23_mul, one_add_one_eq_two, h2, x23_zero]

@[expose] def dg1 (a : F) : Matrix (Fin 3) (Fin 3) F := !![a, 0, 0; 0, 1, 0; 0, 0, 1]

@[expose] def dg2 (a : F) : Matrix (Fin 3) (Fin 3) F := !![1, 0, 0; 0, a, 0; 0, 0, 1]

@[expose] noncomputable def dg1GL (a : F) (ha : a ≠ 0) : GL (Fin 3) F :=
  GeneralLinearGroup.mkOfDetNeZero (dg1 a) (by simpa [dg1, Matrix.det_fin_three] using ha)

@[expose] noncomputable def dg2GL (a : F) (ha : a ≠ 0) : GL (Fin 3) F :=
  GeneralLinearGroup.mkOfDetNeZero (dg2 a) (by simpa [dg2, Matrix.det_fin_three] using ha)

theorem comm_dg1_x12 {a t : F} (ha : a ≠ 0) (hat : a * t = 1 + t) :
    ⁅dg1GL a ha, x12GL t⁆ = x12GL 1 := by
  have h : dg1GL a ha * x12GL t = x12GL 1 * x12GL t * dg1GL a ha := by
    apply Units.ext
    change dg1 a * x12 t = x12 1 * x12 t * dg1 a
    rw [x12_mul]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [dg1, x12, Matrix.mul_apply, Fin.sum_univ_three, hat]
  rw [commutatorElement_def, h]
  group

theorem comm_dg2_x23 {a t : F} (ha : a ≠ 0) (hat : a * t = 1 + t) :
    ⁅dg2GL a ha, x23GL t⁆ = x23GL 1 := by
  have h : dg2GL a ha * x23GL t = x23GL 1 * x23GL t * dg2GL a ha := by
    apply Units.ext
    change dg2 a * x23 t = x23 1 * x23 t * dg2 a
    rw [x23_mul]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [dg2, x23, Matrix.mul_apply, Fin.sum_univ_three, hat]
  rw [commutatorElement_def, h]
  group

end Mat

section Uni

variable {F : Type} [Field F]

@[expose] def IsUniM (M : Matrix (Fin 3) (Fin 3) F) : Prop :=
  M 0 0 = 1 ∧ M 1 1 = 1 ∧ M 2 2 = 1 ∧ M 1 0 = 0 ∧ M 2 0 = 0 ∧ M 2 1 = 0

theorem IsUniM.one : IsUniM (1 : Matrix (Fin 3) (Fin 3) F) := by
  simp [IsUniM]

theorem IsUniM.mul {M N : Matrix (Fin 3) (Fin 3) F} (hM : IsUniM M) (hN : IsUniM N) :
    IsUniM (M * N) := by
  obtain ⟨a0, a1, a2, a3, a4, a5⟩ := hM
  obtain ⟨b0, b1, b2, b3, b4, b5⟩ := hN
  simp [IsUniM, Matrix.mul_apply, Fin.sum_univ_three, a0, a1, a2, a3, a4, a5, b0, b1, b2, b3, b4,
    b5]

theorem IsUniM.eq {M : Matrix (Fin 3) (Fin 3) F} (hM : IsUniM M) :
    M = !![1, M 0 1, M 0 2; 0, 1, M 1 2; 0, 0, 1] := by
  obtain ⟨a0, a1, a2, a3, a4, a5⟩ := hM
  ext i j
  fin_cases i <;> fin_cases j <;> simp [a0, a1, a2, a3, a4, a5]

theorem IsUniM.pow_four (h2 : (2 : F) = 0) {M : Matrix (Fin 3) (Fin 3) F} (hM : IsUniM M) :
    M ^ 4 = 1 := by
  have hsq : M * M = !![1, 0, M 0 1 * M 1 2; 0, 1, 0; 0, 0, 1] := by
    conv_lhs => rw [hM.eq]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
    all_goals first
      | linear_combination (M 0 1) * h2 | linear_combination (M 1 2) * h2
      | linear_combination (M 0 2) * h2
  have h4 : M ^ 4 = (M * M) * (M * M) := by
    rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]
  rw [h4, hsq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  all_goals linear_combination (M 0 1 * M 1 2) * h2

@[expose] def uniSub (h2 : (2 : F) = 0) : Subgroup (GL (Fin 3) F) where
  carrier := {u | IsUniM (u : Matrix (Fin 3) (Fin 3) F)}
  one_mem' := by
    show IsUniM ((1 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)
    rw [Units.val_one]
    exact IsUniM.one
  mul_mem' := fun {a b} ha hb => by
    show IsUniM (((a * b : GL (Fin 3) F)) : Matrix (Fin 3) (Fin 3) F)
    rw [Units.val_mul]
    exact IsUniM.mul ha hb
  inv_mem' := fun {a} ha => by
    have ha' : IsUniM (a : Matrix (Fin 3) (Fin 3) F) := ha
    have h4 : a ^ 4 = 1 := Units.ext (by
      rw [Units.val_pow_eq_pow_val, Units.val_one]
      exact ha'.pow_four h2)
    have hinv : a⁻¹ = a * a * a := inv_eq_of_mul_eq_one_right (by
      calc a * (a * a * a) = a ^ 4 := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
        _ = 1 := h4)
    show IsUniM (((a⁻¹ : GL (Fin 3) F)) : Matrix (Fin 3) (Fin 3) F)
    rw [hinv, Units.val_mul, Units.val_mul]
    exact (ha'.mul ha').mul ha'

theorem uniSub_isPGroup (h2 : (2 : F) = 0) : IsPGroup 2 (uniSub h2) := by
  intro g
  refine ⟨2, ?_⟩
  have hg : IsUniM ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := g.2
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_pow, Units.val_pow_eq_pow_val, Subgroup.coe_one, Units.val_one]
  exact hg.pow_four h2

theorem x12GL_mem_uniSub (h2 : (2 : F) = 0) : x12GL (1 : F) ∈ uniSub h2 := by
  show IsUniM (x12 (1 : F))
  simp [IsUniM, x12]

theorem x23GL_mem_uniSub (h2 : (2 : F) = 0) : x23GL (1 : F) ∈ uniSub h2 := by
  show IsUniM (x23 (1 : F))
  simp [IsUniM, x23]

end Uni

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87.P47PGL
