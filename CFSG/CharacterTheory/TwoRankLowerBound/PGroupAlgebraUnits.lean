module

public import CFSG.CharacterTheory.TwoRankLowerBound.RegularDeterminantPGroup

public section

open scoped Classical

namespace CFSG.TwoRankLowerBound.Helpers

theorem p_group_algebra_isUnit_iff {field group : Type*}
    [Field field] [Group group] [Finite group]
    (prime : ℕ) [Fact prime.Prime] [CharP field prime] (hgroup : IsPGroup prime group)
    (value : MonoidAlgebra field group) :
    IsUnit value ↔ groupAlgebraAugmentation field group value ≠ 0 := by
  let := Fintype.ofFinite group
  rw [groupAlgebra_isUnit_iff_leftMultiplicationDet,
    groupAlgebra_p_group_leftMultiplicationDet prime hgroup, isUnit_iff_ne_zero]
  exact pow_ne_zero_iff (Nat.card_pos.ne')

theorem local_p_group_algebra_isUnit_iff {ring group : Type*}
    [CommRing ring] [IsLocalRing ring] [Group group] [Finite group]
    (prime : ℕ) [Fact prime.Prime] [CharP (IsLocalRing.ResidueField ring) prime]
    (hgroup : IsPGroup prime group) (value : MonoidAlgebra ring group) :
    IsUnit value ↔ IsUnit (groupAlgebraAugmentation ring group value) := by
  rw [← groupAlgebra_isUnit_iff_residue (IsLocalRing.residue ring)
    (fun coefficient => isUnit_iff_ne_zero.trans
      (IsLocalRing.residue_ne_zero_iff_isUnit coefficient)),
    p_group_algebra_isUnit_iff prime hgroup, groupAlgebraAugmentation_map,
    IsLocalRing.residue_ne_zero_iff_isUnit]

theorem local_p_group_algebra_unit_or_complement {ring group : Type*}
    [CommRing ring] [IsLocalRing ring] [Group group] [Finite group]
    (prime : ℕ) [Fact prime.Prime] [CharP (IsLocalRing.ResidueField ring) prime]
    (hgroup : IsPGroup prime group) (value : MonoidAlgebra ring group) :
    IsUnit value ∨ IsUnit (1 - value) := by
  rw [local_p_group_algebra_isUnit_iff prime hgroup,
    local_p_group_algebra_isUnit_iff prime hgroup, map_sub, map_one]
  exact IsLocalRing.isUnit_or_isUnit_one_sub_self _

theorem idempotent_eq_zero_or_one_of_unit_or_complement {ring : Type*} [Ring ring]
    (value : ring) (hidempotent : IsIdempotentElem value)
    (hunit : IsUnit value ∨ IsUnit (1 - value)) : value = 0 ∨ value = 1 := by
  rcases hunit with hunit | hunit
  · exact Or.inr (hunit.mul_left_cancel (by simpa only [mul_one] using hidempotent.eq))
  · left
    have hzero : (1 - value) * value = 0 := by
      rw [sub_mul, one_mul, hidempotent.eq, sub_self]
    exact hunit.mul_left_cancel (hzero.trans (mul_zero _).symm)

theorem local_p_group_algebra_idempotent_eq_zero_or_one {ring group : Type*}
    [CommRing ring] [IsLocalRing ring] [Group group] [Finite group]
    (prime : ℕ) [Fact prime.Prime] [CharP (IsLocalRing.ResidueField ring) prime]
    (hgroup : IsPGroup prime group) (value : MonoidAlgebra ring group)
    (hidempotent : IsIdempotentElem value) : value = 0 ∨ value = 1 :=
  idempotent_eq_zero_or_one_of_unit_or_complement value hidempotent
    (local_p_group_algebra_unit_or_complement prime hgroup value)

end CFSG.TwoRankLowerBound.Helpers
