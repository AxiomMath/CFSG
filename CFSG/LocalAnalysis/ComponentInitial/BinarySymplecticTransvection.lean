module

public import CFSG.LocalAnalysis.ComponentInitial.LinearSymplecticInvolution
public import Mathlib.LinearAlgebra.Transvection.Basic

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Module

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] def binarySymplecticTransvection (B : LinearMap.BilinForm (ZMod 2) V) (hB : B.IsAlt)
    (a : V) : LinearMap.GeneralLinearGroup (ZMod 2) V :=
  LinearMap.GeneralLinearGroup.ofLinearEquiv
    (LinearEquiv.transvection (f := B.flip a) (v := a) (hB a))

variable {B : LinearMap.BilinForm (ZMod 2) V}

theorem binarySymplecticTransvection_apply (hB : B.IsAlt) (a v : V) :
    (binarySymplecticTransvection B hB a : V →ₗ[ZMod 2] V) v = v + B v a • a :=
  rfl

namespace BinarySymplecticTransvection

theorem gl_ext {x y : LinearMap.GeneralLinearGroup (ZMod 2) V}
    (h : ∀ v, (x : V →ₗ[ZMod 2] V) v = (y : V →ₗ[ZMod 2] V) v) : x = y :=
  Units.ext (LinearMap.ext h)

theorem gl_mul_apply (x y : LinearMap.GeneralLinearGroup (ZMod 2) V) (v : V) :
    ((x * y : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) v =
      (x : V →ₗ[ZMod 2] V) ((y : V →ₗ[ZMod 2] V) v) :=
  rfl

theorem gl_one_apply (v : V) :
    ((1 : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) v = v :=
  rfl

theorem gl_apply_inv_apply (g : LinearMap.GeneralLinearGroup (ZMod 2) V) (v : V) :
    (g : V →ₗ[ZMod 2] V) (((g⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) V) :
      V →ₗ[ZMod 2] V) v) = v := by
  rw [← gl_mul_apply, mul_inv_cancel, gl_one_apply]

theorem zmod_two_cases (c : ZMod 2) : c = 0 ∨ c = 1 := by
  revert c
  decide

theorem symm_apply (hB : B.IsAlt) (x y : V) : B y x = B x y := by
  rw [← hB.neg_eq x y, ZMod.neg_eq_self_mod_two]

theorem exists_apply_eq_one (hBn : B.Nondegenerate) {a : V} (ha : a ≠ 0) : ∃ v, B v a = 1 := by
  by_contra h
  push Not at h
  refine ha (hBn.2 a fun v => ?_)
  rcases zmod_two_cases (B v a) with h0 | h1
  · exact h0
  · exact absurd h1 (h v)

theorem transvection_mem_bilinIsometryGroup (hB : B.IsAlt) (a : V) :
    binarySymplecticTransvection B hB a ∈ bilinIsometryGroup B := by
  rw [mem_bilinIsometryGroup]
  intro x y
  simp only [binarySymplecticTransvection_apply, map_add, map_smul, LinearMap.add_apply,
    LinearMap.smul_apply, smul_eq_mul, hB.self_eq_zero a, symm_apply hB y a, mul_zero, add_zero]
  generalize B x y = p
  generalize B x a = q
  generalize B y a = r
  revert p q r
  decide

theorem mul_self (hB : B.IsAlt) (a : V) :
    binarySymplecticTransvection B hB a * binarySymplecticTransvection B hB a = 1 := by
  refine gl_ext fun v => ?_
  rw [gl_mul_apply, gl_one_apply, binarySymplecticTransvection_apply,
    binarySymplecticTransvection_apply]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    hB.self_eq_zero a, mul_zero, add_zero]
  rw [add_assoc, add_self_eq_zero_zmod_two, add_zero]

theorem inv_eq (hB : B.IsAlt) (a : V) :
    (binarySymplecticTransvection B hB a)⁻¹ = binarySymplecticTransvection B hB a :=
  inv_eq_of_mul_eq_one_right (mul_self hB a)

theorem zero_eq_one (hB : B.IsAlt) : binarySymplecticTransvection B hB 0 = 1 :=
  gl_ext fun v => by rw [binarySymplecticTransvection_apply, smul_zero, add_zero, gl_one_apply]

theorem eq_of_eq (hB : B.IsAlt) (hBn : B.Nondegenerate) {a b : V} (ha : a ≠ 0)
    (h : binarySymplecticTransvection B hB a = binarySymplecticTransvection B hB b) : a = b := by
  obtain ⟨v, hv⟩ := exists_apply_eq_one hBn ha
  have hv' := congrArg
    (fun x : LinearMap.GeneralLinearGroup (ZMod 2) V => (x : V →ₗ[ZMod 2] V) v) h
  simp only [binarySymplecticTransvection_apply, hv, one_smul, add_right_inj] at hv'
  rcases zmod_two_cases (B v b) with h0 | h1
  · rw [h0, zero_smul] at hv'
    exact absurd hv' ha
  · rwa [h1, one_smul] at hv'

theorem conj (hB : B.IsAlt) {g : LinearMap.GeneralLinearGroup (ZMod 2) V}
    (hg : g ∈ bilinIsometryGroup B) (a : V) :
    g * binarySymplecticTransvection B hB a * g⁻¹ =
      binarySymplecticTransvection B hB ((g : V →ₗ[ZMod 2] V) a) := by
  refine gl_ext fun v => ?_
  have hiso := hg (((g⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) v) a
  rw [gl_apply_inv_apply] at hiso
  rw [gl_mul_apply, gl_mul_apply, binarySymplecticTransvection_apply,
    binarySymplecticTransvection_apply, map_add, map_smul, gl_apply_inv_apply, hiso]

theorem mul_mul_self (hB : B.IsAlt) (a b : V) :
    binarySymplecticTransvection B hB b * binarySymplecticTransvection B hB a *
        binarySymplecticTransvection B hB b =
      binarySymplecticTransvection B hB (a + B a b • b) := by
  have h := conj hB (transvection_mem_bilinIsometryGroup hB b) a
  rwa [inv_eq, binarySymplecticTransvection_apply] at h

theorem eq_of_mul_eq_one (hB : B.IsAlt) (hBn : B.Nondegenerate) {a b : V} (ha : a ≠ 0)
    (h : binarySymplecticTransvection B hB a * binarySymplecticTransvection B hB b = 1) :
    a = b := by
  refine eq_of_eq hB hBn ha ?_
  rw [← mul_one (binarySymplecticTransvection B hB a), ← mul_self hB b, ← mul_assoc, h,
    one_mul]

theorem orderOf_mul_of_eq_zero (hB : B.IsAlt) (hBn : B.Nondegenerate) {a b : V} (ha : a ≠ 0)
    (hab : a ≠ b) (h : B a b = 0) :
    orderOf (binarySymplecticTransvection B hB a * binarySymplecticTransvection B hB b) = 2 := by
  have hcomm : binarySymplecticTransvection B hB a * binarySymplecticTransvection B hB b *
      binarySymplecticTransvection B hB a = binarySymplecticTransvection B hB b := by
    rw [mul_mul_self, symm_apply hB a b, h, zero_smul, add_zero]
  refine orderOf_eq_prime ?_ fun h1 => hab (eq_of_mul_eq_one hB hBn ha h1)
  rw [sq, ← mul_assoc, hcomm, mul_self]

theorem orderOf_mul_of_eq_one (hB : B.IsAlt) (hBn : B.Nondegenerate) {a b : V}
    (h : B a b = 1) :
    orderOf (binarySymplecticTransvection B hB a * binarySymplecticTransvection B hB b) = 3 := by
  have ha : a ≠ 0 := by
    rintro rfl
    rw [map_zero, LinearMap.zero_apply] at h
    exact absurd h (by decide)
  have hab : binarySymplecticTransvection B hB a * binarySymplecticTransvection B hB b *
      binarySymplecticTransvection B hB a = binarySymplecticTransvection B hB (a + b) := by
    rw [mul_mul_self, symm_apply hB a b, h, one_smul, add_comm]
  have hba : binarySymplecticTransvection B hB b * binarySymplecticTransvection B hB a *
      binarySymplecticTransvection B hB b = binarySymplecticTransvection B hB (a + b) := by
    rw [mul_mul_self, h, one_smul]
  refine orderOf_eq_prime ?_ fun h1 => ?_
  · calc (binarySymplecticTransvection B hB a * binarySymplecticTransvection B hB b) ^ 3 =
          (binarySymplecticTransvection B hB a * binarySymplecticTransvection B hB b *
            binarySymplecticTransvection B hB a) *
          (binarySymplecticTransvection B hB b * binarySymplecticTransvection B hB a *
            binarySymplecticTransvection B hB b) := by
          rw [pow_three]
          simp only [mul_assoc]
      _ = 1 := by rw [hab, hba, mul_self]
  · have hab' := eq_of_mul_eq_one hB hBn ha h1
    rw [hab', hB.self_eq_zero] at h
    exact absurd h (by decide)

theorem apply_adjoint {g : LinearMap.GeneralLinearGroup (ZMod 2) V}
    (hg : g ∈ bilinIsometryGroup B) (hg2 : g ^ 2 = 1) (v w : V) :
    B ((g : V →ₗ[ZMod 2] V) v) w = B v ((g : V →ₗ[ZMod 2] V) w) := by
  have hgg : (g : V →ₗ[ZMod 2] V) ((g : V →ₗ[ZMod 2] V) w) = w := by
    rw [← gl_mul_apply, ← sq, hg2, gl_one_apply]
  calc B ((g : V →ₗ[ZMod 2] V) v) w =
        B ((g : V →ₗ[ZMod 2] V) v) ((g : V →ₗ[ZMod 2] V) ((g : V →ₗ[ZMod 2] V) w)) := by
          rw [hgg]
    _ = B v ((g : V →ₗ[ZMod 2] V) w) := hg _ _

variable [FiniteDimensional (ZMod 2) V]

theorem eq_one_or_eq_transvection (hB : B.IsAlt) (hBn : B.Nondegenerate)
    {g : LinearMap.GeneralLinearGroup (ZMod 2) V} (hg : g ∈ bilinIsometryGroup B)
    (hg2 : g ^ 2 = 1) (hrank : finrank (ZMod 2) (LinearMap.range ((g : V →ₗ[ZMod 2] V) - 1)) ≤ 1) :
    g = 1 ∨ ∃ b : V, b ≠ 0 ∧ g = binarySymplecticTransvection B hB b := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hrank with h0 | h1
  · left
    have hbot := Submodule.finrank_eq_zero.mp h0
    rw [LinearMap.range_eq_bot, sub_eq_zero] at hbot
    exact Units.ext hbot
  · right
    obtain ⟨⟨b, hbN⟩, hb0, hspan⟩ := finrank_eq_one_iff'.mp h1
    have hb : b ≠ 0 := fun h => hb0 (Subtype.ext h)
    have hval : ∀ v, ((g : V →ₗ[ZMod 2] V) - 1) v = 0 ∨ ((g : V →ₗ[ZMod 2] V) - 1) v = b := by
      intro v
      obtain ⟨c, hc⟩ := hspan ⟨_, LinearMap.mem_range_self _ v⟩
      have hc' := congrArg Subtype.val hc
      simp only [SetLike.val_smul] at hc'
      rcases zmod_two_cases c with rfl | rfl
      · left
        rw [← hc', zero_smul]
      · right
        rw [← hc', one_smul]
    obtain ⟨w, hw⟩ := hbN
    have hadj : ∀ v u, B (((g : V →ₗ[ZMod 2] V) - 1) v) u =
        B v (((g : V →ₗ[ZMod 2] V) - 1) u) := by
      intro v u
      simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub, LinearMap.sub_apply,
        apply_adjoint hg hg2]
    have hBb : ∀ v, B v b = B (((g : V →ₗ[ZMod 2] V) - 1) v) w := fun v => by
      rw [hadj, hw]
    have hbw : B b w = 1 := by
      rcases zmod_two_cases (B b w) with h | h
      · refine absurd (hBn.2 b fun v => ?_) hb
        rw [hBb]
        rcases hval v with h' | h'
        · rw [h', map_zero, LinearMap.zero_apply]
        · rw [h', h]
      · exact h
    refine ⟨b, hb, gl_ext fun v => ?_⟩
    have hgv : (g : V →ₗ[ZMod 2] V) v = v + ((g : V →ₗ[ZMod 2] V) - 1) v := by
      rw [LinearMap.sub_apply, Module.End.one_apply, add_sub_cancel]
    rw [hgv, binarySymplecticTransvection_apply, hBb]
    rcases hval v with h' | h'
    · rw [h', map_zero, LinearMap.zero_apply, zero_smul]
    · rw [h', hbw, one_smul]

end BinarySymplecticTransvection

open BinarySymplecticTransvection

end CFSG.LocalAnalysis.ComponentInitial
