module

public import CFSG.LinearAlgebra.LinearGroups.UnitaryBasics

public noncomputable section

namespace CFSG.LocalAnalysis.GorensteinLyons

namespace FourUnitary

open Module CFSG.LocalAnalysis.ComponentInitial CFSG.LinearGroups

section Field

variable {F : Type*} [Field F] (hF : UnitaryFieldData 2 1 F)

theorem bar_eq_sq (a : F) : hF.bar a = a ^ 2 := by
  rw [hF.bar_apply, pow_one]

include hF in
theorem two_eq_zero : (2 : F) = 0 := by
  have := hF.charP
  exact CharTwo.two_eq_zero

include hF in
theorem neg_eq_self (a : F) : -a = a := by
  linear_combination (-a) * two_eq_zero hF

include hF in
theorem pow_three_eq_one {a : F} (ha : a ≠ 0) : a ^ 3 = 1 := by
  have := hF.finite
  have := Fintype.ofFinite F
  have h := FiniteField.pow_card_sub_one_eq_one a ha
  rwa [← Nat.card_eq_fintype_card, hF.card] at h

theorem bar_mul_self {a : F} (ha : a ≠ 0) : hF.bar a * a = 1 := by
  rw [bar_eq_sq, ← pow_succ, pow_three_eq_one hF ha]

end Field

section Transvection

variable {F : Type*} [Field F] {hF : UnitaryFieldData 2 1 F} {W : Type*} [AddCommGroup W]
  [Module F W] {B : W →ₛₗ[hF.bar] W →ₗ[F] F}

theorem transvection_one_apply (v x : W) : hermTransvection B v 1 x = x + B v x • v := by
  rw [hermTransvection_apply, one_mul]

theorem exists_ne_zero_of_ne_zero (hBl : B.SeparatingLeft) {v : W} (hv0 : v ≠ 0) :
    ∃ y, B v y ≠ 0 := by
  by_contra! hz
  exact hv0 (hBl v hz)

theorem transvection_mul_self {v : W} (hv : B v v = 0) :
    hermTransvection B v 1 * hermTransvection B v 1 = 1 := by
  rw [Module.End.mul_eq_comp, hermTransvection_comp B hv,
    show (1 : F) + 1 = 0 by linear_combination two_eq_zero hF, hermTransvection_zero]
  rfl

theorem transvectionGL_mul_self {v : W} (hv : B v v = 0) :
    hermTransvectionGL B hv 1 * hermTransvectionGL B hv 1 = 1 :=
  Units.ext (transvection_mul_self hv)

theorem transvectionGL_ne_one (hBl : B.SeparatingLeft) {v : W} (hv0 : v ≠ 0) (hv : B v v = 0) :
    hermTransvectionGL B hv 1 ≠ 1 := by
  intro h1
  obtain ⟨y, hy⟩ := exists_ne_zero_of_ne_zero hBl hv0
  have h := congrArg (fun g : LinearMap.GeneralLinearGroup F W => (g : W →ₗ[F] W) y) h1
  simp only [coe_hermTransvectionGL, transvection_one_apply, Units.val_one, Module.End.one_apply,
    add_eq_left] at h
  exact smul_ne_zero hy hv0 h

theorem orderOf_transvectionGL (hBl : B.SeparatingLeft) {v : W} (hv0 : v ≠ 0) (hv : B v v = 0) :
    orderOf (hermTransvectionGL B hv 1) = 2 :=
  orderOf_eq_prime (by rw [sq, transvectionGL_mul_self]) (transvectionGL_ne_one hBl hv0 hv)

end Transvection

end FourUnitary

end CFSG.LocalAnalysis.GorensteinLyons
