module

public import CFSG.Mathlib.GroupTheory.Basic
public import CFSG.LocalAnalysis.LargeEvenClassification.CharacteristicAbelianCentralizer
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

open scoped commutatorElement

namespace CFSG.LargeEvenClassification.Helpers

universe groupUniverse

def powerGeneratedSubgroup (Ambient : Type groupUniverse) [Group Ambient] (exponent : ℕ) :
    Subgroup Ambient := Subgroup.closure (Set.range (fun source : Ambient => source ^ exponent))

theorem power_generated_subgroup_characteristic {Ambient : Type groupUniverse} [Group Ambient]
    (exponent : ℕ) : (powerGeneratedSubgroup Ambient exponent).Characteristic := by
  apply Subgroup.characteristic_iff_map_le.mpr
  intro automorphism
  rw [powerGeneratedSubgroup, MonoidHom.map_closure]
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨_, ⟨source, rfl⟩, rfl⟩
  exact Subgroup.subset_closure ⟨automorphism source, (map_pow automorphism source exponent).symm⟩

theorem class_two_commutator_central {Ambient : Type groupUniverse} [Group Ambient]
    [Group.IsNilpotent Ambient] (hclass : Group.nilpotencyClass Ambient ≤ 2) :
    commutator Ambient ≤ Subgroup.center Ambient := by
  have hzero := Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mpr hclass
  have hone : (⊤ : Subgroup Ambient).lowerCentralSeries 1 = commutator Ambient := by
    simpa only [Subgroup.lowerCentralSeries_zero, commutator_def] using
      Subgroup.lowerCentralSeries_succ (⊤ : Subgroup Ambient) 0
  rw [show 2 = 1 + 1 from rfl, Subgroup.lowerCentralSeries_succ, hone] at hzero
  rw [← subgroup_centralizer_top_eq_center]
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hzero

theorem central_commutator_power_left {Ambient : Type groupUniverse} [Group Ambient]
    (first second : Ambient) (hcommute : Commute first ⁅first, second⁆) (exponent : ℕ) :
    ⁅first, second⁆ ^ exponent = ⁅first ^ exponent, second⁆ := by
  induction exponent with
  | zero => simp [commutatorElement_def]
  | succ exponent induction =>
      have hsuccessor : ⁅first ^ (exponent + 1), second⁆ =
          first * ⁅first ^ exponent, second⁆ * first⁻¹ * ⁅first, second⁆ := by
        rw [pow_succ', commutatorElement_def, commutatorElement_def, commutatorElement_def]
        group
      rw [hsuccessor, ← induction, (hcommute.pow_right exponent).eq, pow_succ]
      group

theorem central_commutator_power_right {Ambient : Type groupUniverse} [Group Ambient]
    (first second : Ambient) (hcommute : Commute second ⁅first, second⁆) (exponent : ℕ) :
    ⁅first, second⁆ ^ exponent = ⁅first, second ^ exponent⁆ := by
  apply inv_injective
  rw [← inv_pow, commutatorElement_inv, commutatorElement_inv]
  apply central_commutator_power_left
  rw [← commutatorElement_inv]
  exact hcommute.inv_right

theorem central_commutators_power_generated_abelian
    {Ambient : Type groupUniverse} [Group Ambient]
    (hcentral : commutator Ambient ≤ Subgroup.center Ambient) (exponent : ℕ)
    (hkilled : ∀ first second : Ambient, ⁅first, second⁆ ^ (exponent * exponent) = 1) :
    IsMulCommutative (powerGeneratedSubgroup Ambient exponent) := by
  apply CFSG.subgroup_isMulCommutative_closure
  rintro _ ⟨first, rfl⟩ _ ⟨second, rfl⟩
  have hcommCentral : ⁅first, second⁆ ∈ Subgroup.center Ambient :=
    hcentral (Subgroup.commutator_mem_commutator (by trivial) (by trivial))
  have hleft : Commute first ⁅first, second⁆ := Subgroup.mem_center_iff.mp hcommCentral first
  have hright : Commute second ⁅first ^ exponent, second⁆ := by
    rw [← central_commutator_power_left first second hleft exponent]
    exact (show Commute second ⁅first, second⁆ from
      Subgroup.mem_center_iff.mp hcommCentral second).pow_right exponent
  apply commutatorElement_eq_one_iff_commute.mp
  rw [← central_commutator_power_right (first ^ exponent) second hright exponent,
    ← central_commutator_power_left first second hleft exponent, ← pow_mul]
  exact hkilled first second

theorem two_group_class_two_characteristic_abelian_central_squares
    {Ambient : Type groupUniverse} [Group Ambient] [Finite Ambient]
    (hpgroup : IsPGroup 2 Ambient)
    (hcentral : commutator Ambient ≤ Subgroup.center Ambient)
    (hcharacteristic : ∀ Abelian : Subgroup Ambient, Abelian.Characteristic → IsMulCommutative Abelian →
      Abelian ≤ Subgroup.center Ambient) :
    (∀ first second : Ambient, ⁅first, second⁆ ^ 2 = 1) ∧
      powerGeneratedSubgroup Ambient 2 ≤ Subgroup.center Ambient ∧
      ∀ source : Ambient, source ^ 2 ∈ Subgroup.center Ambient := by
  have hdescend : ∀ steps : ℕ,
      (∀ first second : Ambient, ⁅first, second⁆ ^ (2 ^ (steps + 1)) = 1) →
      ∀ first second : Ambient, ⁅first, second⁆ ^ 2 = 1 := by
    intro steps
    induction steps with
    | zero => simpa only [zero_add, pow_one] using (id :
        (∀ first second : Ambient, ⁅first, second⁆ ^ (2 ^ 1) = 1) →
        ∀ first second : Ambient, ⁅first, second⁆ ^ (2 ^ 1) = 1)
    | succ steps induction =>
        intro hkilled
        have hdivides : 2 ^ (steps + 1 + 1) ∣ 2 ^ (steps + 1) * 2 ^ (steps + 1) := by
          rw [← pow_add]
          exact Nat.pow_dvd_pow 2 (by omega)
        have hab := central_commutators_power_generated_abelian hcentral (2 ^ (steps + 1))
          (fun first second => orderOf_dvd_iff_pow_eq_one.mp
            ((orderOf_dvd_iff_pow_eq_one.mpr (hkilled first second)).trans hdivides))
        have hpowerCentral := hcharacteristic (powerGeneratedSubgroup Ambient (2 ^ (steps + 1)))
          (power_generated_subgroup_characteristic _) hab
        apply induction
        intro first second
        have hcommCentral : ⁅first, second⁆ ∈ Subgroup.center Ambient :=
          hcentral (Subgroup.commutator_mem_commutator (by trivial) (by trivial))
        have hpowerMem : first ^ (2 ^ (steps + 1)) ∈ Subgroup.center Ambient :=
          hpowerCentral (Subgroup.subset_closure ⟨first, rfl⟩)
        rw [central_commutator_power_left first second
          (Subgroup.mem_center_iff.mp hcommCentral first)]
        exact (show Commute (first ^ (2 ^ (steps + 1))) second from
          (Subgroup.mem_center_iff.mp hpowerMem second).symm).commutator_eq
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨size, hcard⟩ := hpgroup.exists_card_eq
  have hkilled : ∀ first second : Ambient, ⁅first, second⁆ ^ 2 = 1 := by
    apply hdescend size
    intro first second
    apply orderOf_dvd_iff_pow_eq_one.mp
    apply (orderOf_dvd_natCard ⁅first, second⁆).trans
    rw [hcard]
    exact Nat.pow_dvd_pow 2 (by omega)
  have hab := central_commutators_power_generated_abelian hcentral 2 (fun first second => by
    rw [pow_mul, hkilled, one_pow])
  have hpowerCentral := hcharacteristic (powerGeneratedSubgroup Ambient 2)
    (power_generated_subgroup_characteristic 2) hab
  exact ⟨hkilled, hpowerCentral, fun source => hpowerCentral (Subgroup.subset_closure ⟨source, rfl⟩)⟩

end CFSG.LargeEvenClassification.Helpers
