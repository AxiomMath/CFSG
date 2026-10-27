module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Minpoly

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Polynomial Module

variable {K : Type*} [Field K] {U : Type*} [AddCommGroup U] [Module K U]

theorem exists_hasEigenvalue_of_pow_card [Fintype K] [FiniteDimensional K U] [Nontrivial U]
    (y : Module.End K U) (hy : y ^ Fintype.card K = y) : ∃ a : K, y.HasEigenvalue a := by
  have h1 : 1 < Fintype.card K := Fintype.one_lt_card
  have hp0 : (X ^ Fintype.card K - X : K[X]) ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero K h1
  have hsplit : (X ^ Fintype.card K - X : K[X]).Splits := by
    rw [splits_iff_card_roots, FiniteField.roots_X_pow_card_sub_X, Finset.card_val,
      Finset.card_univ, FiniteField.X_pow_card_sub_X_natDegree_eq K h1]
  have haeval : aeval y (X ^ Fintype.card K - X : K[X]) = 0 := by
    rw [map_sub, map_pow, aeval_X, hy, sub_self]
  have hms : (minpoly K y).Splits := hsplit.of_dvd hp0 (minpoly.dvd K y haeval)
  have hdeg : (minpoly K y).degree ≠ 0 :=
    (minpoly.degree_pos (IsIntegral.of_finite K y)).ne'
  obtain ⟨a, ha⟩ := hms.exists_eval_eq_zero hdeg
  exact ⟨a, Module.End.hasEigenvalue_of_isRoot ha⟩

theorem exists_eq_smul_of_commute_of_irreducible [Finite K] [FiniteDimensional K U] [Nontrivial U]
    {x y : U ≃ₗ[K] U} (hxy : x * y = y * x)
    (hirr : ∀ W : Submodule K U, (∀ w ∈ W, x w ∈ W) → W = ⊥ ∨ W = ⊤) {m : ℕ}
    (hm : y ^ m = 1) (hmq : m ∣ Nat.card K - 1) : ∃ a : K, ∀ u, y u = a • u := by
  have := Fintype.ofFinite K
  have hq : 1 ≤ Nat.card K := Nat.card_pos
  obtain ⟨k, hk⟩ := hmq
  have hyq : y ^ Fintype.card K = y := by
    rw [← Nat.card_eq_fintype_card, show Nat.card K = (Nat.card K - 1) + 1 by omega, pow_succ,
      hk, pow_mul, hm, one_pow, one_mul]
  set y' : Module.End K U := y.toLinearMap with hy'
  have hy'q : y' ^ Fintype.card K = y' := by
    refine LinearMap.ext fun u => ?_
    rw [Module.End.coe_pow, hy', LinearEquiv.coe_coe, ← LinearEquiv.coe_pow, hyq]
  obtain ⟨a, ha⟩ := exists_hasEigenvalue_of_pow_card y' hy'q
  rw [Module.End.hasEigenvalue_iff] at ha
  have hinv : ∀ w ∈ y'.eigenspace a, x w ∈ y'.eigenspace a := by
    intro w hw
    rw [Module.End.mem_eigenspace_iff] at hw ⊢
    have e : y (x w) = x (y w) := by rw [← LinearEquiv.mul_apply, ← hxy, LinearEquiv.mul_apply]
    have hw' : y w = a • w := hw
    change y (x w) = a • x w
    rw [e, hw', map_smul]
  rcases hirr _ hinv with h | h
  · exact absurd h ha
  · refine ⟨a, fun u => ?_⟩
    have hu : u ∈ y'.eigenspace a := h ▸ Submodule.mem_top
    rw [Module.End.mem_eigenspace_iff] at hu
    exact hu

theorem mem_center_of_eq_smul {X : Type*} [Group X] (ψ : X →* (U ≃ₗ[K] U))
    (hψ : Function.Injective ψ) {y : X} {a : K} (hy : ∀ u, ψ y u = a • u) :
    y ∈ Subgroup.center X := by
  rw [Subgroup.mem_center_iff]
  intro z
  apply hψ
  refine LinearEquiv.ext fun u => ?_
  rw [map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hy, hy, map_smul]

end CFSG.SeitzReduction.SymplecticPilot
