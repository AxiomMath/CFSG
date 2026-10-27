module

public import CFSG.LinearAlgebra.ExtraspecialCyclotomicModule
public import Mathlib.LinearAlgebra.BilinearForm.Basic
public import Mathlib.Algebra.Polynomial.Expand
public import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open Polynomial CFSG.LinearAlgebra

theorem aeval_pow_two_zmod_two {A : Type*} [Ring A] [Algebra (ZMod 2) A] (x : A)
    (P : (ZMod 2)[X]) : aeval x P ^ 2 = aeval (x ^ 2) P := by
  rw [← expand_aeval, ← map_pow, ← ZMod.expand_card, expand_aeval]

theorem aeval_pow_thirtytwo_zmod_two {A : Type*} [Ring A] [Algebra (ZMod 2) A] (x : A)
    (P : (ZMod 2)[X]) : aeval x P ^ 32 = aeval (x ^ 32) P := by
  calc aeval x P ^ 32 = (((((aeval x P) ^ 2) ^ 2) ^ 2) ^ 2) ^ 2 := by simp only [← pow_mul]
    _ = aeval (x ^ 32) P := by
      rw [aeval_pow_two_zmod_two, aeval_pow_two_zmod_two, aeval_pow_two_zmod_two,
        aeval_pow_two_zmod_two, aeval_pow_two_zmod_two]
      simp only [← pow_mul]

section Abstract

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

theorem bilin_aeval_adjoint (b : LinearMap.BilinForm (ZMod 2) W) (x : Module.End (ZMod 2) W)
    (hx : ∀ v w, b (x v) (x w) = b v w) (hx11 : x ^ 11 = 1) (P : (ZMod 2)[X]) (v w : W) :
    b (aeval x P v) w = b v (aeval (x ^ 10) P w) := by
  have hxx : x * x ^ 10 = 1 := by rw [← pow_succ', hx11]
  have hxS : ∀ w : W, x ((x ^ 10) w) = w := fun w => by
    rw [← Module.End.mul_apply, hxx, Module.End.one_apply]
  have hadj : ∀ v w : W, b (x v) w = b v ((x ^ 10) w) := fun v w => by
    conv_lhs => rw [← hxS w]
    exact hx _ _
  have hpow : ∀ n : ℕ, ∀ v w : W, b ((x ^ n) v) w = b v (((x ^ 10) ^ n) w) := by
    intro n
    induction n with
    | zero => intro v w; simp
    | succ n ih =>
      intro v w
      rw [pow_succ x n, Module.End.mul_apply, ih, hadj, pow_succ' (x ^ 10) n,
        Module.End.mul_apply]
  induction P using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, LinearMap.add_apply, map_add, hp, hq]
  | monomial n a =>
    simp only [aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply, map_smul,
      LinearMap.smul_apply, hpow]

theorem pow_thirtythree_of_isometry_of_mem_adjoin (b : LinearMap.BilinForm (ZMod 2) W)
    (hb : ∀ m, (∀ n, b n m = 0) → m = 0) (x : Module.End (ZMod 2) W)
    (hx : ∀ v w, b (x v) (x w) = b v w) (hx11 : x ^ 11 = 1) (c : Module.End (ZMod 2) W)
    (hc : c ∈ Algebra.adjoin (ZMod 2) {x}) (hcb : ∀ v w, b (c v) (c w) = b v w) :
    c ^ 33 = 1 := by
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hc
  obtain ⟨P, hP⟩ := (AlgHom.mem_range _).1 hc
  subst hP
  have h32 : aeval x P ^ 32 = aeval (x ^ 10) P := by
    rw [aeval_pow_thirtytwo_zmod_two, show x ^ 32 = x ^ 10 by
      rw [show 32 = 11 * 2 + 10 by rfl, pow_add, pow_mul, hx11, one_pow, one_mul]]
  have hinv : aeval (x ^ 10) P * aeval x P = 1 := by
    refine LinearMap.ext fun w => sub_eq_zero.1 (hb _ fun v => ?_)
    rw [map_sub, Module.End.mul_apply, ← bilin_aeval_adjoint b x hx hx11, hcb,
      Module.End.one_apply]
    exact sub_self _
  rw [pow_succ, h32, hinv]

end Abstract

variable {Q : Type*} [Group Q] {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem bilin_centralFixed_centralImage (ρ : Representation (ZMod 2) Q V) (z : Q)
    (b : LinearMap.BilinForm (ZMod 2) V) (hzb : ∀ v w, b (ρ z v) (ρ z w) = b v w) :
    (∀ u ∈ centralFixed ρ z, ∀ w ∈ centralImage ρ z, b u w = 0) ∧
    ∀ u ∈ centralFixed ρ z, ∀ w ∈ centralImage ρ z, b w u = 0 := by
  have hu : ∀ u ∈ centralFixed ρ z, ρ z u = u := fun u hu => by
    simpa [centralFixed, sub_eq_zero] using hu
  constructor
  · rintro u hu' _ ⟨v, rfl⟩
    have h := hzb u v
    rw [hu u hu'] at h
    rw [LinearMap.sub_apply, Module.End.one_apply]
    rw [map_sub]
    exact sub_eq_zero.2 h
  · rintro u hu' _ ⟨v, rfl⟩
    have h := hzb v u
    rw [hu u hu'] at h
    rw [LinearMap.sub_apply, Module.End.one_apply]
    exact (map_sub (b.flip u) (ρ z v) v).trans (sub_eq_zero.2 h)

theorem scalar_pow_thirtythree_of_isometry
    (ρ : Representation (ZMod 2) Q V) (z : Q) (hz : ρ z ^ 11 = 1)
    (hcompl : IsCompl (centralFixed ρ z) (centralImage ρ z))
    (b : LinearMap.BilinForm (ZMod 2) V) (hb : b.Nondegenerate)
    (hzb : ∀ v w, b (ρ z v) (ρ z w) = b v w)
    (a : Module.End (ZMod 2) V) (hab : ∀ v w, b (a v) (a w) = b v w)
    (c : centralImageAlgebra ρ z)
    (hc : ∀ w : centralImage ρ z,
      (((c : Module.End (ZMod 2) (centralImage ρ z)) w : centralImage ρ z) : V) = a w) :
    c ^ 33 = 1 := by
  obtain ⟨-, hWU⟩ := bilin_centralFixed_centralImage ρ z b hzb
  have hxn : ∀ (n : ℕ) (w : centralImage ρ z),
      (((centralImageOp ρ z ^ n) w : centralImage ρ z) : V) = (ρ z ^ n) w := by
    intro n
    induction n with
    | zero => intro w; rfl
    | succ n ih => intro w; rw [pow_succ, Module.End.mul_apply, pow_succ, Module.End.mul_apply,
        ih, coe_centralImageOp_apply]
  refine Subtype.ext ?_
  change (c : Module.End (ZMod 2) (centralImage ρ z)) ^ 33 = 1
  refine pow_thirtythree_of_isometry_of_mem_adjoin (b.restrict (centralImage ρ z)) ?_
    (centralImageOp ρ z) (fun v w => hzb v w) ?_ _ c.2 (fun v w => ?_)
  · intro m hm
    refine Subtype.ext ?_
    refine hb.2 _ fun v => ?_
    obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.1 (hcompl.sup_eq_top ▸ Submodule.mem_top (x := v))
    rw [map_add, LinearMap.add_apply, (bilin_centralFixed_centralImage ρ z b hzb).1 u hu m m.2,
      zero_add]
    exact hm ⟨w, hw⟩
  · refine LinearMap.ext fun w => Subtype.ext ?_
    rw [hxn, hz]
    rfl
  · change b (((c : Module.End (ZMod 2) (centralImage ρ z)) v : centralImage ρ z) : V)
      (((c : Module.End (ZMod 2) (centralImage ρ z)) w : centralImage ρ z) : V) = b v w
    rw [hc, hc]
    exact hab v w

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
