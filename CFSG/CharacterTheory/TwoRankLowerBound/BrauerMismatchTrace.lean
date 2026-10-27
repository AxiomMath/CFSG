module

public import CFSG.CharacterTheory.TwoRankLowerBound.BrauerNonconjugateTrace
public import CFSG.CharacterTheory.TwoRankLowerBound.LeftTranslationBimoduleTransport

public section

open scoped Classical

namespace CFSG.TwoRankLowerBound.Helpers

theorem subgroupBimodule_mismatch_section_trace_zero {ring group : Type*}
    [CommRing ring] [IsDomain ring] [IsLocalRing ring] [Group group] [Fintype group]
    (prime : ℕ) [Fact prime.Prime] [CharP (IsLocalRing.ResidueField ring) prime]
    (rightPrimary leftPrimary leftRegular : group)
    (rightRegular : Subgroup.centralizer (Subgroup.zpowers rightPrimary : Set group))
    (leftExponent rightExponent : ℕ)
    (hleftPrimary : orderOf leftPrimary ∣ prime ^ leftExponent)
    (hrightPrimary : orderOf rightPrimary ∣ prime ^ rightExponent)
    (hleftCommute : Commute leftPrimary leftRegular)
    (period : ℕ) (periodUnit root : ringˣ) (hunit : (periodUnit : ring) = period)
    (hroot : IsPrimitiveRoot (root : ring) period)
    (hleftPeriod : leftRegular ^ period = 1) (hrightPeriod : rightRegular.val ^ period = 1)
    (left : MonoidAlgebra ring group)
    (right : MonoidAlgebra ring (Subgroup.centralizer (Subgroup.zpowers rightPrimary : Set group)))
    (hleft : ∀ element : group, Commute left (MonoidAlgebra.single element 1))
    (hright : ∀ element : Subgroup.centralizer (Subgroup.zpowers rightPrimary : Set group),
      Commute right (MonoidAlgebra.single element 1))
    (hleftIdempotent : IsIdempotentElem left) (hrightIdempotent : IsIdempotentElem right)
    (hzero : MonoidAlgebra.mapRingHom (Subgroup.centralizer (Subgroup.zpowers rightPrimary : Set group))
      (IsLocalRing.residue ring)
      (subgroupCoefficientProjection (Subgroup.centralizer (Subgroup.zpowers rightPrimary : Set group)) left * right) = 0) :
    LinearMap.trace ring (MonoidAlgebra ring group)
      (subgroupBimoduleProjection (Subgroup.centralizer (Subgroup.zpowers rightPrimary : Set group)) left right *
        Representation.ofMulAction ring (Equiv.Perm group) group
          (groupTwoSidedPermutationHom group (leftPrimary * leftRegular, rightPrimary * rightRegular.val))) = 0 := by
  by_cases hconjugate : IsConj rightPrimary leftPrimary
  · obtain ⟨conjugator, hconjugator⟩ := isConj_iff.mp hconjugate
    let conjugated := (MulAut.conj conjugator⁻¹) leftRegular
    have hprimaryTransport : (MulAut.conj conjugator⁻¹) leftPrimary = rightPrimary := by
      rw [← hconjugator]
      change conjugator⁻¹ * (conjugator * rightPrimary * conjugator⁻¹) * (conjugator⁻¹)⁻¹ = rightPrimary
      group
    have hcommute : Commute rightPrimary conjugated := by
      have hequal := hleftCommute.map (MulAut.conj conjugator⁻¹)
      rw [hprimaryTransport] at hequal
      exact hequal
    have hperiod : conjugated ^ period = 1 := by
      change ((MulAut.conj conjugator⁻¹) leftRegular) ^ period = 1
      rw [← map_pow, hleftPeriod, map_one]
    have hregularPeriod : (groupTwoSidedPermutationHom group (conjugated, rightRegular.val)) ^ period = 1 := by
      rw [groupTwoSidedPermutation_power, hperiod, hrightPeriod]
      exact map_one (groupTwoSidedPermutationHom group)
    have htrace := brauerBimodule_equal_primary_trace_zero prime rightPrimary rightExponent hrightPrimary
      left right hleft hright hleftIdempotent hrightIdempotent hzero conjugated rightRegular
      hcommute period periodUnit root hunit hroot hregularPeriod
    have htransport := subgroupBimodule_twoSided_trace_conjugate_left
      (Subgroup.centralizer (Subgroup.zpowers rightPrimary : Set group)) left right hleft
      (leftPrimary * leftRegular) (rightPrimary * rightRegular.val) conjugator⁻¹
    have hproduct : conjugator⁻¹ * (leftPrimary * leftRegular) * (conjugator⁻¹)⁻¹ =
        rightPrimary * conjugated := by
      change (MulAut.conj conjugator⁻¹) (leftPrimary * leftRegular) = rightPrimary * conjugated
      rw [map_mul, hprimaryTransport]
    rw [hproduct] at htransport
    exact htransport.symm.trans htrace
  · have hregularPeriod : (groupTwoSidedPermutationHom group (leftRegular, rightRegular.val)) ^ period = 1 := by
      rw [groupTwoSidedPermutation_power, hleftPeriod, hrightPeriod]
      exact map_one (groupTwoSidedPermutationHom group)
    exact subgroupBimodule_nonconjugate_primary_trace_zero prime rightPrimary leftPrimary leftRegular rightRegular
      leftExponent rightExponent hleftPrimary hrightPrimary hleftCommute
      (fun hequal => hconjugate hequal.symm) period periodUnit root hunit hroot hregularPeriod
      left right hleft hright hleftIdempotent hrightIdempotent

end CFSG.TwoRankLowerBound.Helpers
