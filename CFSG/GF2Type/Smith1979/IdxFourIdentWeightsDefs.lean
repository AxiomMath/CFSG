module

public import CFSG.GF2Type.Smith1979.IdxFourIdentMonDefs
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.RepresentationTheory.Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.IdxFour

open CFSG.GF2Type.Smith1979.GammaU

@[expose] noncomputable def rep {A : Type*} [Group A] (ρ : A →* G12) :
    Representation (ZMod 2) A V12 :=
  LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp ρ

@[simp] theorem rep_apply {A : Type*} [Group A] (ρ : A →* G12) (a : A) (v : V12) :
    rep ρ a v = ρ a v := rfl

@[expose] def f0Bilin : LinearMap.BilinMap (ZMod 2) V12 (ZMod 2) :=
  LinearMap.mk₂ (ZMod 2) f0
    (fun x x' y => by
      simp only [f0, Pi.add_apply, Finset.sum_add_distrib.symm]
      refine Finset.sum_congr rfl fun i _ => by ring)
    (fun a x y => by
      simp only [f0, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => by ring)
    (fun x y y' => by
      simp only [f0, Pi.add_apply, Finset.sum_add_distrib.symm]
      refine Finset.sum_congr rfl fun i _ => by ring)
    (fun a x y => by
      simp only [f0, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => by ring)

@[expose] noncomputable def q0Form : QuadraticForm (ZMod 2) V12 where
  toFun := q0
  toFun_smul a x := by
    have h : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
    rcases h a with rfl | rfl
    · simp only [zero_smul, zero_mul]
      simp [q0]
    · simp
  exists_companion' := ⟨f0Bilin, fun x y => by
    have h := polar_q0 x y
    simp only [QuadraticMap.polar] at h
    show q0 (x + y) = q0 x + q0 y + f0 x y
    rw [← h]
    ring⟩

@[simp] theorem q0Form_apply (x : V12) : q0Form x = q0 x := rfl

theorem polar_q0Form (x y : V12) : QuadraticMap.polar q0Form x y = f0 x y := polar_q0 x y

end CFSG.GF2Type.Smith1979.IdxFour
