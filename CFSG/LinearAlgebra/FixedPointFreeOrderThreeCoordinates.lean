module

public import CFSG.LinearAlgebra.FixedPointFreeOrderThreeField
public import CFSG.CharacterTheory.Semidihedral.ElementaryActionTransport

public section

namespace CFSG.LinearAlgebra

open CFSG.Semidihedral.ElementaryActionTransport

variable {W : Type*} [CommGroup W] [Finite W]

noncomputable def frobeniusOmega : OmegaField ≃+* OmegaField :=
  Classical.choose exists_omegaField_frobenius

@[simp] theorem frobeniusOmega_apply (x : OmegaField) : frobeniusOmega x = x ^ 2 :=
  Classical.choose_spec exists_omegaField_frobenius x

theorem exists_omega_coordinates_of_order_three
    (hW : ∀ w : W, w ^ 2 = 1)
    (n : ℕ) (hcard : Nat.card W = 2 ^ (2 * n))
    (z : MulAut W) (hz : orderOf z = 3)
    (hfix : ∀ w : W, z w = w → w = 1) :
    ∃ e : W ≃* Multiplicative (Fin n → OmegaField),
      ∀ w : W,
        Multiplicative.toAdd (e (z w)) =
          omega • Multiplicative.toAdd (e w) := by
  classical
  haveI hEA : IsElementaryAbelian 2 W :=
    { toIsMulCommutative := inferInstance
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hW }
  let V := Additive W
  haveI : Finite V := inferInstance
  have hfin : Module.finrank (ZMod 2) V = 2 * n := by
    have h := card_eq_prime_pow_finrank (p := 2) (R := W)
    rw [hcard] at h
    exact (Nat.pow_right_injective (by norm_num : 1 < 2) h).symm
  let zGL : LinearMap.GeneralLinearGroup (ZMod 2) V := autEquivGL (p := 2) (R := W) z
  have hzGLord : orderOf zGL = 3 := by
    have h1 : orderOf (autEquivGL (p := 2) (R := W) z) = orderOf z :=
      orderOf_injective (autEquivGL (p := 2) (R := W)).toMonoidHom
        (autEquivGL (p := 2) (R := W)).injective z
    exact h1.trans hz
  have hzGLfix : ∀ v : V, (zGL : V →ₗ[ZMod 2] V) v = v → v = 0 := by
    intro v hv
    have hv' : (autToGL (p := 2) (R := W) z : Module.End (ZMod 2) V)
        (Additive.ofMul (Additive.toMul v)) = Additive.ofMul (Additive.toMul v) := hv
    rw [autToGL_apply] at hv'
    have hww : z (Additive.toMul v) = Additive.toMul v := Additive.ofMul.injective hv'
    have hv1 : Additive.toMul v = 1 := hfix (Additive.toMul v) hww
    change Additive.ofMul (Additive.toMul v) = 0
    rw [hv1]
    rfl
  letI : Module OmegaField V := omegaModule zGL hzGLord hzGLfix
  haveI : IsScalarTower (ZMod 2) OmegaField V :=
    omegaModule_isScalarTower zGL hzGLord hzGLfix
  have homega : ∀ v : V, omega • v = (zGL : V →ₗ[ZMod 2] V) v :=
    omegaModule_omega_smul zGL hzGLord hzGLfix
  have hfindim : Module.finrank OmegaField V = n := by
    have hmul := Module.finrank_mul_finrank (ZMod 2) OmegaField V
    rw [finrank_omegaField, hfin] at hmul
    omega
  haveI : Module.Finite OmegaField V := Module.Finite.of_finite
  let b : Module.Basis (Fin n) OmegaField V :=
    Module.finBasisOfFinrankEq OmegaField V hfindim
  let eLin : V ≃ₗ[OmegaField] (Fin n → OmegaField) := b.equivFun
  let e : W ≃* Multiplicative (Fin n → OmegaField) :=
    { toFun := fun w => Multiplicative.ofAdd (eLin (Additive.ofMul w))
      invFun := fun x => Additive.toMul (eLin.symm (Multiplicative.toAdd x))
      left_inv := fun w => by simp
      right_inv := fun x => by simp
      map_mul' := fun a b => by
        apply congrArg Multiplicative.ofAdd
        change eLin (Additive.ofMul (a * b)) =
          eLin (Additive.ofMul a) + eLin (Additive.ofMul b)
        rw [ofMul_mul, map_add] }
  refine ⟨e, ?_⟩
  intro w
  change eLin (Additive.ofMul (z w)) = omega • eLin (Additive.ofMul w)
  have hzapp : (zGL : V →ₗ[ZMod 2] V) (Additive.ofMul w) = Additive.ofMul (z w) := by
    change (autToGL (p := 2) (R := W) z : Module.End (ZMod 2) V)
        (Additive.ofMul w) = Additive.ofMul (z w)
    rw [autToGL_apply]
  rw [← hzapp, ← homega, map_smul]

theorem exists_omega_coordinates_of_order_three_rank_six
    (hW : ∀ w : W, w ^ 2 = 1)
    (hcard : Nat.card W = 2 ^ 6)
    (z : MulAut W) (hz : orderOf z = 3)
    (hfix : ∀ w : W, z w = w → w = 1) :
    ∃ e : W ≃* Multiplicative (Fin 3 → OmegaField),
      ∀ w : W,
        Multiplicative.toAdd (e (z w)) =
          omega • Multiplicative.toAdd (e w) := by
  have hcard' : Nat.card W = 2 ^ (2 * 3) := by
    rw [show 2 * 3 = 6 by norm_num]
    exact hcard
  exact exists_omega_coordinates_of_order_three hW 3 hcard' z hz hfix

end CFSG.LinearAlgebra
