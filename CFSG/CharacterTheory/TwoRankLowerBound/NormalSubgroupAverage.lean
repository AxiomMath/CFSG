module

public import CFSG.CharacterTheory.TwoRankLowerBound.AbelianPGroupAlgebra

public section

open scoped BigOperators Classical

namespace CFSG.TwoRankLowerBound.Helpers

@[expose] noncomputable def normalSubgroupAverage {ring group : Type*} [CommRing ring] [Group group]
    (subgroup : Subgroup group) [Fintype subgroup] (cardUnit : ringˣ) : MonoidAlgebra ring group :=
  (cardUnit⁻¹ : ringˣ) • ∑ element : subgroup, MonoidAlgebra.single element.val 1

theorem normalSubgroupAverage_mul_single {ring group : Type*} [CommRing ring] [Group group]
    (subgroup : Subgroup group) [Fintype subgroup] (cardUnit : ringˣ) (element : subgroup) :
    normalSubgroupAverage subgroup cardUnit * MonoidAlgebra.single element.val 1 =
      normalSubgroupAverage subgroup cardUnit := by
  unfold normalSubgroupAverage
  rw [smul_mul_assoc, Finset.sum_mul]
  congr 1
  simp only [MonoidAlgebra.single_mul_single, mul_one, ← Subgroup.coe_mul]
  exact (Equiv.sum_comp (Equiv.mulRight element) (fun member : subgroup =>
    MonoidAlgebra.single member.val 1))

theorem single_mul_normalSubgroupAverage {ring group : Type*} [CommRing ring] [Group group]
    (subgroup : Subgroup group) [Fintype subgroup] (cardUnit : ringˣ) (element : subgroup) :
    MonoidAlgebra.single element.val 1 * normalSubgroupAverage subgroup cardUnit =
      normalSubgroupAverage subgroup cardUnit := by
  unfold normalSubgroupAverage
  rw [mul_smul_comm, Finset.mul_sum]
  congr 1
  simp only [MonoidAlgebra.single_mul_single, one_mul, ← Subgroup.coe_mul]
  exact (Equiv.sum_comp (Equiv.mulLeft element) (fun member : subgroup =>
    MonoidAlgebra.single member.val 1))

theorem normalSubgroupAverage_idempotent {ring group : Type*} [CommRing ring] [Group group]
    (subgroup : Subgroup group) [Fintype subgroup] (cardUnit : ringˣ)
    (hcard : (cardUnit : ring) = Nat.card subgroup) :
    IsIdempotentElem (normalSubgroupAverage subgroup cardUnit) := by
  change normalSubgroupAverage subgroup cardUnit * normalSubgroupAverage subgroup cardUnit = _
  conv_lhs => rhs; unfold normalSubgroupAverage
  rw [mul_smul_comm, Finset.mul_sum]
  simp only [normalSubgroupAverage_mul_single, Finset.sum_const, Finset.card_univ]
  rw [← Nat.card_eq_fintype_card, ← Nat.cast_smul_eq_nsmul ring, ← hcard]
  change ((cardUnit⁻¹ : ringˣ) : ring) • ((cardUnit : ring) • normalSubgroupAverage subgroup cardUnit) = _
  rw [smul_smul, Units.inv_mul, one_smul]

theorem normalSubgroupAverage_central {ring group : Type*} [CommRing ring] [Group group]
    [Fintype group]
    (subgroup : Subgroup group) [subgroup.Normal] [Fintype subgroup] (cardUnit : ringˣ) :
    ∀ value : MonoidAlgebra ring group, Commute (normalSubgroupAverage subgroup cardUnit) value := by
  intro value
  have hsingle : ∀ element : group,
      Commute (normalSubgroupAverage subgroup cardUnit) (MonoidAlgebra.single element 1) := by
    intro element
    change normalSubgroupAverage subgroup cardUnit * MonoidAlgebra.single element 1 =
      MonoidAlgebra.single element 1 * normalSubgroupAverage subgroup cardUnit
    unfold normalSubgroupAverage
    rw [smul_mul_assoc, mul_smul_comm, Finset.sum_mul, Finset.mul_sum]
    congr 1
    simp only [MonoidAlgebra.single_mul_single, mul_one]
    apply Fintype.sum_equiv (MulAut.conjNormal (H := subgroup) element⁻¹).toEquiv
    intro member
    congr 1
    change member.val * element = element * ((MulAut.conjNormal (H := subgroup) element⁻¹) member).val
    rw [MulAut.conjNormal_apply]
    group
  conv_rhs => rw [← groupAlgebra_sum_single value]
  apply Commute.sum_right
  intro element _
  have hequal : MonoidAlgebra.single element (value.coeff element) =
      value.coeff element • (MonoidAlgebra.single element 1 : MonoidAlgebra ring group) := by
    rw [MonoidAlgebra.smul_single, smul_eq_mul, mul_one]
  rw [hequal]
  exact (hsingle element).smul_right _

end CFSG.TwoRankLowerBound.Helpers
