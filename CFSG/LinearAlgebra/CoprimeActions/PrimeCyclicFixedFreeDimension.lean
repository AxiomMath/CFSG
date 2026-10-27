module


public import Mathlib.Algebra.Field.ZMod
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.GroupTheory.PGroup
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

public section

namespace CFSG.LinearAlgebra.CoprimeActions.PrimeCyclicFixedFreeDimension

theorem orderOf_two_dvd_finrank (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (σ : W ≃ₗ[ZMod 2] W) (hσ : σ ^ p = 1)
    (hfix : LinearMap.ker (σ.toLinearMap - 1) = ⊥) :
    orderOf (2 : ZMod p) ∣ Module.finrank (ZMod 2) W := by
  classical
  have hord : orderOf σ ∣ p := orderOf_dvd_of_pow_eq_one hσ
  have hcard : Nat.card (Subgroup.zpowers σ) = orderOf σ := Nat.card_zpowers σ
  have hpg : IsPGroup p (Subgroup.zpowers σ) := by
    rcases (Nat.dvd_prime hp.out).1 hord with h | h
    · exact IsPGroup.of_card (n := 0) (by rw [hcard, h]; simp)
    · exact IsPGroup.of_card (n := 1) (by rw [hcard, h]; simp)
  haveI : Finite W := Module.finite_of_finite (ZMod 2)
  have hmod := hpg.card_modEq_card_fixedPoints (α := W)
  have hfp : Nat.card (MulAction.fixedPoints (Subgroup.zpowers σ) W) = 1 := by
    have : MulAction.fixedPoints (Subgroup.zpowers σ) W = {0} := by
      ext v
      simp only [MulAction.mem_fixedPoints, Set.mem_singleton_iff]
      constructor
      · intro h
        have h1 : σ v = v := h ⟨σ, Subgroup.mem_zpowers σ⟩
        have : v ∈ LinearMap.ker (σ.toLinearMap - 1) := by simp [h1]
        rw [hfix] at this
        simpa using this
      · rintro rfl m
        exact smul_zero _
    rw [this]; simp
  rw [hfp, Module.natCard_eq_pow_finrank (K := ZMod 2) (V := W)] at hmod
  have h2 : (2 : ZMod p) ^ Module.finrank (ZMod 2) W = 1 := by
    have := (ZMod.natCast_eq_natCast_iff _ _ _).2 hmod
    simpa using this
  exact orderOf_dvd_of_pow_eq_one h2

end CFSG.LinearAlgebra.CoprimeActions.PrimeCyclicFixedFreeDimension
