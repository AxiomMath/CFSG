module

public import CFSG.CharacterTheory.TwoRankLowerBound.PermutationCoefficientRing
public import CFSG.CharacterTheory.TwoRankLowerBound.CentralSummandBimoduleTrace
public import CFSG.CharacterTheory.TwoRankLowerBound.TwoSidedPermutation

public section

open scoped BigOperators Classical

namespace CFSG.TwoRankLowerBound.Helpers

theorem groupTwoSidedPermutation_power {group : Type*} [Group group] (left right : group) (exponent : ℕ) :
    (groupTwoSidedPermutationHom group (left, right)) ^ exponent =
      groupTwoSidedPermutationHom group (left ^ exponent, right ^ exponent) := by
  rw [← map_pow]
  rfl

theorem groupTwoSidedPermutation_no_fixedpoint {group : Type*} [Group group]
    (left right : group) (hnotconjugate : ¬ IsConj left right) (element : group) :
    groupTwoSidedPermutationHom group (left, right) element ≠ element := by
  intro hequal
  change left * element * right⁻¹ = element at hequal
  have hconjugate : left = element * right * element⁻¹ := by
    calc
      _ = (left * element * right⁻¹) * right * element⁻¹ := by group
      _ = _ := by rw [hequal]
  exact hnotconjugate ((isConj_iff.mpr ⟨element, hconjugate.symm⟩).symm)

theorem groupTwoSidedPermutation_prime_power_order {group : Type*} [Group group] [Finite group]
    (prime : ℕ) (hprime : prime.Prime) (left right : group) (leftExponent rightExponent : ℕ)
    (hleft : orderOf left ∣ prime ^ leftExponent) (hright : orderOf right ∣ prime ^ rightExponent) :
    ∃ exponent : ℕ, orderOf (groupTwoSidedPermutationHom group (left, right)) = prime ^ exponent := by
  have hleftPower : left ^ (prime ^ max leftExponent rightExponent) = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp (hleft.trans (Nat.pow_dvd_pow prime (Nat.le_max_left _ _)))
  have hrightPower : right ^ (prime ^ max leftExponent rightExponent) = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp (hright.trans (Nat.pow_dvd_pow prime (Nat.le_max_right _ _)))
  have hperiod : (groupTwoSidedPermutationHom group (left, right)) ^ (prime ^ max leftExponent rightExponent) = 1 := by
    rw [groupTwoSidedPermutation_power, hleftPower, hrightPower]
    exact map_one (groupTwoSidedPermutationHom group)
  obtain ⟨exponent, _, horder⟩ := (Nat.dvd_prime_pow hprime).mp (orderOf_dvd_of_pow_eq_one hperiod)
  exact ⟨exponent, horder⟩

theorem groupTwoSidedPermutation_complement_period {group : Type*} [Group group] [Finite group]
    (left right : group) :
    (groupTwoSidedPermutationHom group (left, right)) ^ (orderOf left * orderOf right) = 1 := by
  rw [groupTwoSidedPermutation_power]
  have hleft : left ^ (orderOf left * orderOf right) = 1 := by
    rw [pow_mul, pow_orderOf_eq_one, one_pow]
  have hright : right ^ (orderOf left * orderOf right) = 1 := by
    rw [pow_mul', pow_orderOf_eq_one, one_pow]
  rw [hleft, hright]
  exact map_one (groupTwoSidedPermutationHom group)

theorem complex_local_central_idempotent_section_trace_zero {group : Type*} [Group group] [Fintype group]
    (ring : Subring ℂ) [IsLocalRing ring] (prime : ℕ) [Fact prime.Prime]
    [CharP (IsLocalRing.ResidueField ring) prime]
    (coefficient : MonoidAlgebra ℂ group) (hintegral : ∀ element, coefficient.coeff element ∈ ring)
    (hcentral : ∀ other, Commute coefficient other) (hidempotent : IsIdempotentElem coefficient)
    (leftPrimary rightPrimary leftRegular rightRegular : group) (leftExponent rightExponent : ℕ)
    (hleftPrimary : orderOf leftPrimary ∣ prime ^ leftExponent)
    (hrightPrimary : orderOf rightPrimary ∣ prime ^ rightExponent)
    (hleftRegular : Nat.Coprime prime (orderOf leftRegular))
    (hrightRegular : Nat.Coprime prime (orderOf rightRegular))
    (hleftCommute : Commute leftPrimary leftRegular) (hrightCommute : Commute rightPrimary rightRegular)
    (hnotconjugate : ¬ IsConj leftPrimary rightPrimary)
    (hroots : ∀ root : ℂ, root ^ (orderOf leftRegular * orderOf rightRegular) = 1 → root ∈ ring) :
    LinearMap.trace ℂ (MonoidAlgebra ℂ group)
      (groupAlgebraTwoSidedOperator coefficient (leftPrimary * leftRegular) (rightPrimary * rightRegular)) = 0 := by
  let integralCoefficient := liftGroupAlgebraCoefficients ring coefficient hintegral
  have hembedding := liftGroupAlgebraCoefficients_map ring coefficient hintegral
  have hintegralCentral : ∀ other, Commute integralCoefficient other := by
    intro other
    apply groupAlgebraCoefficientEmbedding_injective ring
    rw [map_mul, map_mul, hembedding]
    exact (hcentral _).eq
  have hintegralIdempotent : IsIdempotentElem integralCoefficient := by
    change integralCoefficient * integralCoefficient = integralCoefficient
    apply groupAlgebraCoefficientEmbedding_injective ring
    rw [map_mul, hembedding]
    exact hidempotent.eq
  let projection := Algebra.lmul ring (MonoidAlgebra ring group) integralCoefficient
  let primary := groupTwoSidedPermutationHom group (leftPrimary, rightPrimary)
  let complement := groupTwoSidedPermutationHom group (leftRegular, rightRegular)
  obtain ⟨exponent, hprimaryOrder⟩ := groupTwoSidedPermutation_prime_power_order prime Fact.out
    leftPrimary rightPrimary leftExponent rightExponent hleftPrimary hrightPrimary
  have hparts : Commute primary complement :=
    (Commute.prod hleftCommute hrightCommute).map (groupTwoSidedPermutationHom group)
  have htrace := complex_local_cyclicPermutation_summand_trace_zero ring prime primary complement exponent
    hprimaryOrder (groupTwoSidedPermutation_no_fixedpoint leftPrimary rightPrimary hnotconjugate)
    hparts (orderOf leftRegular * orderOf rightRegular)
    (Nat.mul_pos (orderOf_pos leftRegular) (orderOf_pos rightRegular))
    ((Fact.out : prime.Prime).coprime_iff_not_dvd.mp (hleftRegular.mul_right hrightRegular))
    (groupTwoSidedPermutation_complement_period leftRegular rightRegular) hroots projection
    (by
      change projection * projection = projection
      rw [← map_mul]
      exact congrArg (Algebra.lmul ring (MonoidAlgebra ring group)) hintegralIdempotent.eq)
    (central_groupAlgebra_projection_commute_twoSided integralCoefficient hintegralCentral leftPrimary rightPrimary)
    (central_groupAlgebra_projection_commute_twoSided integralCoefficient hintegralCentral leftRegular rightRegular)
  have hproduct : complement * primary = groupTwoSidedPermutationHom group
      (leftPrimary * leftRegular, rightPrimary * rightRegular) := by
    rw [hparts.eq.symm, ← map_mul]
    rfl
  change LinearMap.trace ℂ (MonoidAlgebra ℂ group)
    (permutationCoefficientExtension ring.subtype
      (Algebra.lmul ring (MonoidAlgebra ring group) integralCoefficient) *
      Representation.ofMulAction ℂ (Equiv.Perm group) group (complement * primary)) = 0 at htrace
  rw [permutationCoefficientExtension_leftMultiplication, hembedding, hproduct,
    groupTwoSidedPermutation_representation, ← mul_assoc] at htrace
  exact htrace

end CFSG.TwoRankLowerBound.Helpers
