module

public import CFSG.CharacterTheory.TwoRankLowerBound.BrauerBimoduleReduction
public import CFSG.CharacterTheory.TwoRankLowerBound.CyclicFixedBasisPeriodicTrace
public import CFSG.CharacterTheory.TwoRankLowerBound.TwoSidedPermutation

public section

open scoped Classical

namespace CFSG.TwoRankLowerBound.Helpers

theorem subgroupBimoduleProjection_commute_twoSided {ring group : Type*}
    [CommRing ring] [Group group] (subgroup : Subgroup group)
    (left : MonoidAlgebra ring group) (right : MonoidAlgebra ring subgroup)
    (hleft : ∀ element : group, Commute left (MonoidAlgebra.single element 1))
    (hright : ∀ element : subgroup, Commute right (MonoidAlgebra.single element 1))
    (leftElement : group) (rightElement : subgroup) :
    Commute (subgroupBimoduleProjection subgroup left right)
      (Representation.ofMulAction ring (Equiv.Perm group) group
        (groupTwoSidedPermutationHom group (leftElement, rightElement.val))) := by
  rw [groupTwoSidedPermutation_representation]
  change subgroupBimoduleProjection subgroup left right *
      (Algebra.lmul ring (MonoidAlgebra ring group) (MonoidAlgebra.single leftElement 1) *
        LinearMap.mulRight ring (MonoidAlgebra.single rightElement.val⁻¹ 1)) = _
  apply LinearMap.ext
  intro value
  let included := MonoidAlgebra.mapDomainRingHom ring subgroup.subtype right
  have hrightCommute : Commute included (MonoidAlgebra.single rightElement.val⁻¹ 1) := by
    have hequal := (hright rightElement⁻¹).map (MonoidAlgebra.mapDomainRingHom ring subgroup.subtype)
    have hsingle : MonoidAlgebra.mapDomainRingHom ring subgroup.subtype
        (MonoidAlgebra.single rightElement⁻¹ 1) = MonoidAlgebra.single rightElement.val⁻¹ 1 := by
      rw [MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_single]
      rfl
    rw [hsingle] at hequal
    exact hequal
  simp only [Module.End.mul_apply, subgroupBimoduleProjection_apply]
  change left * (MonoidAlgebra.single leftElement 1 * (value * MonoidAlgebra.single rightElement.val⁻¹ 1)) *
      included = MonoidAlgebra.single leftElement 1 *
        ((left * value * included) * MonoidAlgebra.single rightElement.val⁻¹ 1)
  calc
    _ = (left * MonoidAlgebra.single leftElement 1) * value *
        (MonoidAlgebra.single rightElement.val⁻¹ 1 * included) := by simp only [mul_assoc]
    _ = (MonoidAlgebra.single leftElement 1 * left) * value *
        (included * MonoidAlgebra.single rightElement.val⁻¹ 1) := by
          rw [(hleft leftElement).eq, hrightCommute.eq]
    _ = _ := by simp only [mul_assoc]

theorem brauerBimodule_equal_primary_trace_zero {ring group : Type*}
    [CommRing ring] [IsDomain ring] [IsLocalRing ring] [Group group] [Fintype group]
    (prime : ℕ) [Fact prime.Prime] [CharP (IsLocalRing.ResidueField ring) prime]
    (primary : group) (exponent : ℕ) (hprimary : orderOf primary ∣ prime ^ exponent)
    (left : MonoidAlgebra ring group)
    (right : MonoidAlgebra ring (Subgroup.centralizer (Subgroup.zpowers primary : Set group)))
    (hleft : ∀ element : group, Commute left (MonoidAlgebra.single element 1))
    (hright : ∀ element : Subgroup.centralizer (Subgroup.zpowers primary : Set group),
      Commute right (MonoidAlgebra.single element 1))
    (hleftIdempotent : IsIdempotentElem left) (hrightIdempotent : IsIdempotentElem right)
    (hzero : MonoidAlgebra.mapRingHom (Subgroup.centralizer (Subgroup.zpowers primary : Set group))
      (IsLocalRing.residue ring)
      (subgroupCoefficientProjection (Subgroup.centralizer (Subgroup.zpowers primary : Set group)) left * right) = 0)
    (leftRegular : group) (rightRegular : Subgroup.centralizer (Subgroup.zpowers primary : Set group))
    (hleftCommute : Commute primary leftRegular) (period : ℕ) (periodUnit root : ringˣ)
    (hunit : (periodUnit : ring) = period) (hroot : IsPrimitiveRoot (root : ring) period)
    (hregularPeriod : (groupTwoSidedPermutationHom group (leftRegular, rightRegular.val)) ^ period = 1) :
    LinearMap.trace ring (MonoidAlgebra ring group)
      (subgroupBimoduleProjection (Subgroup.centralizer (Subgroup.zpowers primary : Set group)) left right *
        Representation.ofMulAction ring (Equiv.Perm group) group
          (groupTwoSidedPermutationHom group (primary * leftRegular, primary * rightRegular.val))) = 0 := by
  let cyclic := Subgroup.zpowers primary
  let : CommGroup cyclic := IsCyclic.commGroup
  let : MulAction cyclic group := subgroupConjugationAction cyclic
  have hcyclic : IsPGroup prime cyclic := IsPGroup.of_card_dvd_pow (by rw [Nat.card_zpowers]; exact hprimary)
  let generator : cyclic := ⟨primary, Subgroup.mem_zpowers primary⟩
  have hgenerator : ∀ member : cyclic, ∃ power : ℕ, generator ^ power = member := by
    intro member
    obtain ⟨power, _, hequal⟩ := Finset.mem_image.mp
      (((isOfFinOrder_of_finite primary).mem_zpowers_iff_mem_range_orderOf).mp member.property)
    exact ⟨power, Subtype.ext hequal⟩
  let projection := subgroupBimoduleProjection (Subgroup.centralizer (cyclic : Set group)) left right
  let representation := Representation.ofMulAction ring (Equiv.Perm group) group
  let regularPermutation := groupTwoSidedPermutationHom group (leftRegular, rightRegular.val)
  let operator := representation regularPermutation
  have hoperatorPeriod : operator ^ period = 1 := by
    rw [← map_pow, hregularPeriod, map_one]
  have hprimaryRepresentation : Representation.ofMulAction ring cyclic group generator =
      representation (groupTwoSidedPermutationHom group (primary, primary)) := by
    rw [subgroupConjugation_representation_eq_twoSided, groupTwoSidedPermutation_representation]
    rfl
  have hprojectionPrimary : Commute projection (Representation.ofMulAction ring cyclic group generator) :=
    brauerBimoduleProjection_equivariant cyclic left right hleft generator
  have hprojectionOperator : Commute projection operator :=
    subgroupBimoduleProjection_commute_twoSided _ left right hleft hright leftRegular rightRegular
  have hrightCommute : Commute primary rightRegular.val :=
    Subgroup.mem_centralizer_iff.mp rightRegular.property primary (Subgroup.mem_zpowers primary)
  have hparts : Commute (groupTwoSidedPermutationHom group (primary, primary)) regularPermutation :=
    (Commute.prod hleftCommute hrightCommute).map (groupTwoSidedPermutationHom group)
  have hprimaryOperator : Commute operator (Representation.ofMulAction ring cyclic group generator) := by
    rw [hprimaryRepresentation]
    exact (hparts.map representation).symm
  have hzeroReduction : permutationFixedBasisReduction (group := cyclic) (IsLocalRing.residue ring) projection = 0 :=
    brauerBimodule_zero_fixedBasis_reduction (IsLocalRing.residue ring) cyclic left right hright hzero
  have htrace := finite_cyclic_zero_fixedBasis_periodic_trace prime hcyclic generator hgenerator period
    periodUnit root hunit hroot operator projection hoperatorPeriod
    (subgroupBimoduleProjection_idempotent _ left right hleftIdempotent hrightIdempotent)
    hprojectionOperator hprojectionPrimary hprimaryOperator hzeroReduction
  rw [hprimaryRepresentation, mul_assoc, ← map_mul] at htrace
  have hequal : regularPermutation * groupTwoSidedPermutationHom group (primary, primary) =
      groupTwoSidedPermutationHom group (primary * leftRegular, primary * rightRegular.val) := by
    rw [← hparts.eq, ← map_mul]
    rfl
  rw [hequal] at htrace
  exact htrace

end CFSG.TwoRankLowerBound.Helpers
