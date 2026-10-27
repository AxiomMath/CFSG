module

public import CFSG.CharacterTheory.BlockSectionOrthogonality.PrimaryParts
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat

public section

open CFSG
namespace CFSG.BlockSectionOrthogonality.Helpers

theorem primaryPart_period_divisible {index : Type*} [Fintype index]
    (permutation primary : Equiv.Perm index) (prime : ℕ) (hprime : prime.Prime)
    (hprimary : BlocksIsPPart prime permutation primary)
    (hNoFixed : ∀ index, primary index ≠ index)
    (index : index) (period : ℕ) (hPeriod : (permutation ^ period) index = index) :
    prime ∣ period := by
  classical
  by_contra hNotDivides
  rcases hprimary with ⟨regular, hProduct, hProduct', ⟨power, hOrder⟩, hPositive, hCoprime⟩
  have hCommute : Commute primary regular := hProduct.trans hProduct'.symm
  have hFactorCoprime : (orderOf primary).Coprime (orderOf regular) := by
    rw [hOrder]
    exact hCoprime.symm.pow_left power
  have hPowerCoprime : (orderOf (primary ^ period)).Coprime (orderOf (regular ^ period)) :=
    hFactorCoprime.of_dvd (orderOf_pow_dvd period) (orderOf_pow_dvd period)
  have hProductPower : primary ^ period * regular ^ period = permutation ^ period := by
    rw [← hCommute.mul_pow, hProduct]
  obtain ⟨exponent, hExponent⟩ := primaryPart_eq_power_of_coprime_factors hProductPower
    (hCommute.pow_pow period period) hPowerCoprime
  have hPrimaryFixed : (primary ^ period) index = index := by
    rw [← hExponent]
    exact Equiv.Perm.pow_apply_eq_self_of_apply_eq_self hPeriod exponent
  have hPeriodCoprime : period.Coprime (orderOf primary) := by
    rw [hOrder]
    exact ((hprime.coprime_iff_not_dvd.mpr hNotDivides).symm).pow_right power
  have hSupport := Equiv.Perm.support_pow_coprime hPeriodCoprime
  have hPrimarySupport : index ∈ primary.support := by
    simpa using hNoFixed index
  rw [← hSupport] at hPrimarySupport
  exact (Equiv.Perm.mem_support.mp hPrimarySupport) hPrimaryFixed

noncomputable def cycleRepresentative {index : Type*} (permutation : Equiv.Perm index)
    (point : index) : index :=
  (Quotient.mk (Equiv.Perm.SameCycle.setoid permutation) point).out

theorem cycleRepresentative_sameCycle {index : Type*} (permutation : Equiv.Perm index)
    (index : index) : permutation.SameCycle (cycleRepresentative permutation index) index := by
  exact Quotient.exact (Quotient.out_eq
    (Quotient.mk (Equiv.Perm.SameCycle.setoid permutation) index))

theorem cycleRepresentative_apply {index : Type*} (permutation : Equiv.Perm index)
    (index : index) : cycleRepresentative permutation (permutation index) =
      cycleRepresentative permutation index := by
  unfold cycleRepresentative
  congr 1
  apply Quotient.sound
  exact (Equiv.Perm.SameCycle.refl permutation index).apply_left

theorem permutation_period_positive {index : Type*} [Fintype index]
    (permutation : Equiv.Perm index) (index : index) :
    0 < Function.minimalPeriod permutation index := by
  have hPeriod : Function.IsPeriodicPt permutation (orderOf permutation) index := by
    change permutation^[orderOf permutation] index = index
    rw [← Equiv.Perm.coe_pow, pow_orderOf_eq_one]
    rfl
  exact hPeriod.minimalPeriod_pos (orderOf_pos permutation)

theorem cycleOffset_exists {index : Type*} [Fintype index]
    (permutation : Equiv.Perm index) (index : index) :
    ∃ offset : ℕ, offset < Function.minimalPeriod permutation
      (cycleRepresentative permutation index) ∧
      (permutation ^ offset) (cycleRepresentative permutation index) = index := by
  classical
  obtain ⟨exponent, hPositive, hBound, hExponent⟩ :=
    Equiv.Perm.SameCycle.exists_pow_eq permutation
      (cycleRepresentative_sameCycle permutation index)
  refine ⟨exponent % Function.minimalPeriod permutation (cycleRepresentative permutation index),
    Nat.mod_lt _ (permutation_period_positive permutation _), ?_⟩
  rw [Equiv.Perm.coe_pow, Function.iterate_mod_minimalPeriod_eq,
    ← Equiv.Perm.coe_pow]
  exact hExponent

noncomputable def cycleOffset {index : Type*} [Fintype index]
    (permutation : Equiv.Perm index) (index : index) : ℕ :=
  (cycleOffset_exists permutation index).choose

theorem cycleOffset_lt {index : Type*} [Fintype index]
    (permutation : Equiv.Perm index) (index : index) :
    cycleOffset permutation index < Function.minimalPeriod permutation
      (cycleRepresentative permutation index) :=
  (cycleOffset_exists permutation index).choose_spec.1

theorem cycleOffset_spec {index : Type*} [Fintype index]
    (permutation : Equiv.Perm index) (index : index) :
    (permutation ^ cycleOffset permutation index) (cycleRepresentative permutation index) = index :=
  (cycleOffset_exists permutation index).choose_spec.2

theorem cycleOffset_apply {index : Type*} [Fintype index]
    (permutation : Equiv.Perm index) (index : index) :
    cycleOffset permutation (permutation index) =
      (cycleOffset permutation index + 1) % Function.minimalPeriod permutation
        (cycleRepresentative permutation index) := by
  have hBound := cycleOffset_lt permutation (permutation index)
  rw [cycleRepresentative_apply] at hBound
  apply (Function.iterate_eq_iterate_iff_of_lt_minimalPeriod hBound
    (Nat.mod_lt _ (permutation_period_positive permutation _))).mp
  rw [Function.iterate_mod_minimalPeriod_eq]
  have hNext := cycleOffset_spec permutation (permutation index)
  rw [cycleRepresentative_apply, Equiv.Perm.coe_pow] at hNext
  rw [hNext, Function.iterate_succ_apply', ← Equiv.Perm.coe_pow, cycleOffset_spec]

theorem cycleRootColor_apply {index : Type*} [Fintype index]
    {ring : Type*} [Monoid ring] (permutation : Equiv.Perm index)
    (prime : ℕ) (root : ring) (hroot : root ^ prime = 1)
    (hPeriods : ∀ index, prime ∣ Function.minimalPeriod permutation index) (index : index) :
    root ^ cycleOffset permutation (permutation index) = root * root ^ cycleOffset permutation index := by
  rw [cycleOffset_apply]
  have hPeriodRoot : root ^ Function.minimalPeriod permutation
      (cycleRepresentative permutation index) = 1 := by
    obtain ⟨factor, hFactor⟩ := hPeriods (cycleRepresentative permutation index)
    rw [hFactor, pow_mul, hroot, one_pow]
  rw [← pow_eq_pow_mod _ hPeriodRoot, pow_succ']

end CFSG.BlockSectionOrthogonality.Helpers
