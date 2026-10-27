module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.NoZeroSMulDivisors.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.Tactic.ContinuousFunctionalCalculus

public section

namespace CFSG.GroupTheory.SteinbergBK

theorem p_group_linear_fixed_vector {p : ℕ} [hp : Fact p.Prime] {P : Type*} [Group P] [Finite P]
    (hP : IsPGroup p P) {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    [FiniteDimensional (ZMod p) V] [Nontrivial V]
    (ρ : P →* LinearMap.GeneralLinearGroup (ZMod p) V) :
    ∃ v : V, v ≠ 0 ∧ ∀ g : P, (ρ g : V →ₗ[ZMod p] V) v = v := by
  let _ : MulAction P V :=
    { smul := fun g v => (ρ g : V →ₗ[ZMod p] V) v
      one_smul := fun v => by
        change (ρ 1 : V →ₗ[ZMod p] V) v = v
        rw [map_one]
        rfl
      mul_smul := fun g h v => by
        change (ρ (g * h) : V →ₗ[ZMod p] V) v =
          (ρ g : V →ₗ[ZMod p] V) ((ρ h : V →ₗ[ZMod p] V) v)
        rw [map_mul]
        rfl }
  have : Finite V := Module.finite_of_finite (ZMod p)
  have hcard : p ∣ Nat.card V := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod]
    exact dvd_pow_self p Module.finrank_pos.ne'
  have h0 : (0 : V) ∈ MulAction.fixedPoints P V := fun g =>
    show (ρ g : V →ₗ[ZMod p] V) 0 = 0 from map_zero _
  obtain ⟨v, hv, hne⟩ := hP.exists_fixed_point_of_prime_dvd_card_of_fixed_point V hcard h0
  exact ⟨v, fun h => hne h.symm, fun g => hv g⟩

end CFSG.GroupTheory.SteinbergBK
