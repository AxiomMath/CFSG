module

public import Mathlib.Algebra.DualNumber

import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.OddStandard.AltStdSec.SylowSn

abbrev R8 : Type := DualNumber (DualNumber (DualNumber ℤ))

noncomputable def eR : Fin 3 → R8 := fun j =>
  if j = 0 then TrivSqZeroExt.inl (TrivSqZeroExt.inl DualNumber.eps)
  else if j = 1 then TrivSqZeroExt.inl DualNumber.eps
  else DualNumber.eps

theorem eR_mul_self (j : Fin 3) : eR j * eR j = 0 := by
  fin_cases j <;> ext <;> simp [eR]

@[expose] noncomputable def sigR : R8 := eR 0 * eR 1 + eR 0 * eR 2 + eR 1 * eR 2

theorem sigR_mul_self : sigR * sigR = 0 := by
  have h0 := eR_mul_self 0
  have h1 := eR_mul_self 1
  have h2 := eR_mul_self 2
  unfold sigR
  linear_combination (eR 1 * eR 1 + eR 2 * eR 2 + 2 * eR 1 * eR 2) * h0 +
    (eR 2 * eR 2 + 2 * eR 0 * eR 2) * h1 + (2 * eR 0 * eR 1) * h2

private def dualSumHom {A : Type*} [AddCommMonoid A] (f : A →+ ℤ) : DualNumber A →+ ℤ where
  toFun x := f x.fst + f x.snd
  map_zero' := by simp
  map_add' x y := by simp; omega

private theorem dualSumHom_apply {A : Type*} [AddCommMonoid A] (f : A →+ ℤ) (x : DualNumber A) :
    dualSumHom f x = f x.fst + f x.snd := by
  simp [dualSumHom]

noncomputable def sR : R8 →+ ℤ := dualSumHom (dualSumHom (dualSumHom (AddMonoidHom.id ℤ)))

theorem sR_prod_eR (J : Finset (Fin 3)) : sR (∏ j ∈ J, eR j) = 1 := by
  have hJ : J = ∅ ∨ J = {0} ∨ J = {1} ∨ J = {2} ∨ J = {0, 1} ∨ J = {0, 2} ∨ J = {1, 2} ∨
      J = {0, 1, 2} := by
    revert J
    decide
  rcases hJ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [sR, dualSumHom_apply, eR]

theorem sR_cast_add_mul_sigR (a b : ℤ) : sR ((a : R8) + (b : R8) * sigR) = a + 3 * b := by
  simp [sR, dualSumHom_apply, sigR, eR]
  omega

end CFSG.OddStandard.AltStdSec.SylowSn
