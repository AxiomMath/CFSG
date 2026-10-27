module


public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal

public section

namespace CFSG.LocalAnalysis.RankThreeUC.ProofSupport.InvertibleAnticonjugateEvenDimension

open Module

theorem even {F W : Type*} [Field F] [AddCommGroup W] [Module F W] [FiniteDimensional F W]
    (h2 : (2 : F) ≠ 0) (a j : W ≃ₗ[F] W)
    (h : j.toLinearMap.comp a.toLinearMap = (-a.toLinearMap).comp j.toLinearMap) :
    Even (Module.finrank F W) := by
  have hneg : (-a.toLinearMap) = (-1 : F) • a.toLinearMap := by simp
  have hd := congrArg LinearMap.det h
  rw [LinearMap.det_comp, hneg, LinearMap.det_comp, LinearMap.det_smul] at hd
  have ha : LinearMap.det a.toLinearMap ≠ 0 := by
    have := LinearMap.det_comp a.toLinearMap a.symm.toLinearMap
    intro h0
    have h1 : LinearMap.det (a.toLinearMap ∘ₗ a.symm.toLinearMap) = 1 := by
      have : a.toLinearMap ∘ₗ a.symm.toLinearMap = LinearMap.id := by ext; simp
      rw [this]; simp
    rw [this, h0] at h1; simp at h1
  have hj : LinearMap.det j.toLinearMap ≠ 0 := by
    have := LinearMap.det_comp j.toLinearMap j.symm.toLinearMap
    intro h0
    have h1 : LinearMap.det (j.toLinearMap ∘ₗ j.symm.toLinearMap) = 1 := by
      have : j.toLinearMap ∘ₗ j.symm.toLinearMap = LinearMap.id := by ext; simp
      rw [this]; simp
    rw [this, h0] at h1; simp at h1
  have h3 : (-1 : F) ^ finrank F W = 1 := by
    have e : LinearMap.det j.toLinearMap * LinearMap.det a.toLinearMap =
        ((-1 : F) ^ finrank F W * LinearMap.det a.toLinearMap) * LinearMap.det j.toLinearMap := hd
    have hne : LinearMap.det j.toLinearMap * LinearMap.det a.toLinearMap ≠ 0 := mul_ne_zero hj ha
    have h0 : ((-1 : F) ^ finrank F W - 1) *
        (LinearMap.det j.toLinearMap * LinearMap.det a.toLinearMap) = 0 := by
      linear_combination -e
    rcases mul_eq_zero.mp h0 with h0 | h0
    · exact sub_eq_zero.mp h0
    · exact absurd h0 hne
  by_contra hodd
  rw [Nat.not_even_iff_odd] at hodd
  rw [hodd.neg_one_pow] at h3
  apply h2
  linear_combination -h3
