module

public import CFSG.CharacterTheory.TwoRankLowerBound.PGroupAlgebraUnits

public section

open scoped Classical

namespace CFSG.TwoRankLowerBound.Helpers

theorem p_group_augmentation_le_jacobson {field group : Type*}
    [Field field] [Group group] [Finite group] (prime : ℕ) [Fact prime.Prime] [CharP field prime]
    (hgroup : IsPGroup prime group) :
    RingHom.ker (groupAlgebraAugmentation field group) ≤ Ring.jacobson (MonoidAlgebra field group) := by
  intro value hvalue
  rw [← Ideal.jacobson_bot]
  apply (Ideal.mem_jacobson_iff (I := ⊥)).mpr
  intro multiplier
  have hunit : IsUnit (1 + multiplier * value) := by
    rw [p_group_algebra_isUnit_iff prime hgroup, map_add, map_mul, hvalue, map_one, mul_zero, add_zero]
    exact one_ne_zero
  obtain ⟨unit, hunitValue⟩ := hunit
  refine ⟨(unit⁻¹ : (MonoidAlgebra field group)ˣ), ?_⟩
  apply Ideal.mem_bot.mpr
  have hequal : (unit⁻¹ : (MonoidAlgebra field group)ˣ) * (1 + multiplier * value) = 1 := by
    rw [← hunitValue]
    exact Units.inv_mul unit
  rw [mul_add, mul_one, ← mul_assoc] at hequal
  rw [add_comm] at hequal
  exact sub_eq_zero.mpr hequal

theorem ideal_pow_mono {ring : Type*} [Semiring ring] (left right : Ideal ring)
    (hcontains : left ≤ right) (exponent : ℕ) : left ^ exponent ≤ right ^ exponent := by
  induction exponent with
  | zero => exact le_refl _
  | succ exponent hinduction =>
    change left ^ exponent * left ≤ right ^ exponent * right
    exact Ideal.mul_mono hinduction hcontains

theorem p_group_augmentation_nilpotent {field group : Type*}
    [Field field] [Group group] [Finite group] (prime : ℕ) [Fact prime.Prime] [CharP field prime]
    (hgroup : IsPGroup prime group) :
    IsNilpotent (RingHom.ker (groupAlgebraAugmentation field group)) := by
  let : IsArtinianRing (MonoidAlgebra field group) := IsArtinianRing.of_finite field _
  obtain ⟨exponent, hpower⟩ :=
    IsSemiprimaryRing.isNilpotent (R := MonoidAlgebra field group)
  refine ⟨exponent, ?_⟩
  apply le_antisymm _ bot_le
  exact (ideal_pow_mono _ _ (p_group_augmentation_le_jacobson (field := field) prime hgroup) exponent).trans
    (by simpa only [hpower, Ideal.zero_eq_bot] using (le_refl (⊥ : Ideal (MonoidAlgebra field group))))

theorem p_group_augmentation_element_nilpotent {field group : Type*}
    [Field field] [Group group] [Finite group] (prime : ℕ) [Fact prime.Prime] [CharP field prime]
    (hgroup : IsPGroup prime group) (value : MonoidAlgebra field group)
    (hzero : groupAlgebraAugmentation field group value = 0) : IsNilpotent value := by
  obtain ⟨exponent, hpower⟩ := p_group_augmentation_nilpotent (field := field) prime hgroup
  refine ⟨exponent, ?_⟩
  have hmember := Ideal.pow_mem_pow (I := RingHom.ker (groupAlgebraAugmentation field group)) hzero exponent
  rw [hpower, Ideal.zero_eq_bot, Ideal.mem_bot] at hmember
  exact hmember

end CFSG.TwoRankLowerBound.Helpers
