module

public import CFSG.CharacterTheory.TwoRankLowerBound.BrauerEqualPrimaryTrace
public import CFSG.CharacterTheory.TwoRankLowerBound.TwoSidedSectionTrace

public section

open scoped Classical

namespace CFSG.TwoRankLowerBound.Helpers

theorem element_mem_centralizer_zpowers {group : Type*} [Group group] (element : group) :
    element ∈ Subgroup.centralizer (Subgroup.zpowers element : Set group) := by
  rw [Subgroup.mem_centralizer_iff]
  intro member hmember
  obtain ⟨exponent, hexponent⟩ := Subgroup.mem_zpowers_iff.mp hmember
  rw [← hexponent]
  exact (Commute.self_zpow element exponent).eq.symm

theorem subgroupBimodule_nonconjugate_primary_trace_zero {ring group : Type*}
    [CommRing ring] [IsDomain ring] [IsLocalRing ring] [Group group] [Fintype group]
    (prime : ℕ) [Fact prime.Prime] [CharP (IsLocalRing.ResidueField ring) prime]
    (rightPrimary leftPrimary leftRegular : group)
    (rightRegular : Subgroup.centralizer (Subgroup.zpowers rightPrimary : Set group))
    (leftExponent rightExponent : ℕ)
    (hleftPrimary : orderOf leftPrimary ∣ prime ^ leftExponent)
    (hrightPrimary : orderOf rightPrimary ∣ prime ^ rightExponent)
    (hleftCommute : Commute leftPrimary leftRegular)
    (hnotconjugate : ¬ IsConj leftPrimary rightPrimary)
    (period : ℕ) (periodUnit root : ringˣ) (hunit : (periodUnit : ring) = period)
    (hroot : IsPrimitiveRoot (root : ring) period)
    (hregularPeriod : (groupTwoSidedPermutationHom group (leftRegular, rightRegular.val)) ^ period = 1)
    (left : MonoidAlgebra ring group)
    (right : MonoidAlgebra ring (Subgroup.centralizer (Subgroup.zpowers rightPrimary : Set group)))
    (hleft : ∀ element : group, Commute left (MonoidAlgebra.single element 1))
    (hright : ∀ element : Subgroup.centralizer (Subgroup.zpowers rightPrimary : Set group),
      Commute right (MonoidAlgebra.single element 1))
    (hleftIdempotent : IsIdempotentElem left) (hrightIdempotent : IsIdempotentElem right) :
    LinearMap.trace ring (MonoidAlgebra ring group)
      (subgroupBimoduleProjection (Subgroup.centralizer (Subgroup.zpowers rightPrimary : Set group)) left right *
        Representation.ofMulAction ring (Equiv.Perm group) group
          (groupTwoSidedPermutationHom group (leftPrimary * leftRegular, rightPrimary * rightRegular.val))) = 0 := by
  let projection := subgroupBimoduleProjection
    (Subgroup.centralizer (Subgroup.zpowers rightPrimary : Set group)) left right
  let primary := groupTwoSidedPermutationHom group (leftPrimary, rightPrimary)
  let complement := groupTwoSidedPermutationHom group (leftRegular, rightRegular.val)
  have hrightCommute : Commute rightPrimary rightRegular.val :=
    Subgroup.mem_centralizer_iff.mp rightRegular.property rightPrimary (Subgroup.mem_zpowers rightPrimary)
  have hparts : Commute primary complement :=
    (Commute.prod hleftCommute hrightCommute).map (groupTwoSidedPermutationHom group)
  obtain ⟨exponent, hprimaryOrder⟩ := groupTwoSidedPermutation_prime_power_order prime Fact.out
    leftPrimary rightPrimary leftExponent rightExponent hleftPrimary hrightPrimary
  have htrace := cyclicPermutation_summand_trace_zero prime primary complement exponent hprimaryOrder
    (groupTwoSidedPermutation_no_fixedpoint leftPrimary rightPrimary hnotconjugate) hparts
    period hregularPeriod periodUnit root hunit hroot projection
    (subgroupBimoduleProjection_idempotent _ left right hleftIdempotent hrightIdempotent)
    (subgroupBimoduleProjection_commute_twoSided _ left right hleft hright leftPrimary
      ⟨rightPrimary, element_mem_centralizer_zpowers rightPrimary⟩)
    (subgroupBimoduleProjection_commute_twoSided _ left right hleft hright leftRegular rightRegular)
  have hequal : complement * primary = groupTwoSidedPermutationHom group
      (leftPrimary * leftRegular, rightPrimary * rightRegular.val) := by
    rw [← hparts.eq, ← map_mul]
    rfl
  rw [hequal] at htrace
  exact htrace

end CFSG.TwoRankLowerBound.Helpers
