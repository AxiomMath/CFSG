module

public import CFSG.CharacterTheory.TwoRankLowerBound.BrauerBimoduleReduction
public import CFSG.CharacterTheory.TwoRankLowerBound.NormalPQuotientNilpotent
public import CFSG.CharacterTheory.TwoRankLowerBound.CentralSubgroupProjection

public section

open scoped BigOperators Classical

namespace CFSG.TwoRankLowerBound.Helpers

theorem groupAlgebra_quotient_coeff_sum {ring source target : Type*}
    [CommRing ring] [Group source] [Fintype source] [Group target]
    (quotient : source →* target) (value : MonoidAlgebra ring source) (element : target) :
    (MonoidAlgebra.mapDomainRingHom ring quotient value).coeff element =
      ∑ member : source, if quotient member = element then value.coeff member else 0 := by
  conv_lhs => rw [← groupAlgebra_sum_single value]
  simp only [map_sum, MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_single,
    MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, MonoidAlgebra.coeff_single, Finsupp.single_apply]

set_option backward.isDefEq.respectTransparency false in
theorem normal_p_invariant_quotient_zero_of_outside_centralizer {field group : Type*}
    [Field field] [Group group] [Fintype group] (prime : ℕ) [Fact prime.Prime] [CharP field prime]
    (subgroup : Subgroup group) [subgroup.Normal] (hgroup : IsPGroup prime subgroup)
    (value : MonoidAlgebra field group) (hinvariant : subgroupConjugationInvariant subgroup value)
    (hzero : ∀ element ∈ Subgroup.centralizer (subgroup : Set group), value.coeff element = 0) :
    MonoidAlgebra.mapDomainRingHom field (QuotientGroup.mk' subgroup) value = 0 := by
  ext element
  rw [groupAlgebra_quotient_coeff_sum, MonoidAlgebra.coeff_zero, Finsupp.zero_apply]
  let : MulAction subgroup group := subgroupConjugationAction subgroup
  let weight : group → field := fun member =>
    if QuotientGroup.mk' subgroup member = element then value.coeff member else 0
  have hweight : ∀ (conjugator : subgroup) (member : group), weight (conjugator • member) = weight member := by
    intro conjugator member
    change (if QuotientGroup.mk' subgroup (conjugator.val * member * conjugator.val⁻¹) = element then
      value.coeff (conjugator.val * member * conjugator.val⁻¹) else 0) = _
    have hconjugator : QuotientGroup.mk' subgroup conjugator.val = 1 :=
      (QuotientGroup.eq_one_iff conjugator.val).mpr conjugator.property
    rw [hinvariant conjugator member, map_mul, map_mul, map_inv, hconjugator, inv_one, one_mul, mul_one]
  have hsum := p_group_invariant_sum_fixedPoints prime hgroup weight hweight
  calc
    _ = ∑ member : group, weight member := by
      apply Finset.sum_congr rfl
      intro member _
      dsimp only [weight]
      split_ifs <;> rfl
    _ = 0 := hsum.trans ?_
  apply Finset.sum_eq_zero
  intro member _
  by_cases hfixed : member ∈ MulAction.fixedPoints subgroup group
  · rw [ite_eq_left hfixed]
    have hcentral := (conjugation_fixedPoints_iff_centralizer subgroup member).mp hfixed
    simp only [weight, hzero member hcentral, ite_self]
  · rw [ite_eq_right hfixed]

theorem centralCharacterResidueHom_zero_of_reduction_nilpotent {G : Type*}
    [Group G] [Fintype G] (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    (value : centralCoefficientSubring (G := G) (localizedComplexIntegerRing ideal))
    (hnilpotent : IsNilpotent (centralCoefficientReductionHom ideal value)) (label : basis.index) :
    centralCharacterResidueHom basis ideal label value = 0 := by
  let : Field (ComplexAlgebraicIntegers ⧸ ideal) := Ideal.Quotient.field ideal
  obtain ⟨exponent, hpower⟩ := hnilpotent
  have hzero : centralCoefficientReductionHom ideal (value ^ exponent) = 0 := by
    rw [map_pow, hpower]
  have hresidue := centralCharacterResidueHom_zero_of_coefficient_reduction_zero basis ideal
    (value ^ exponent) hzero label
  rw [map_pow] at hresidue
  exact IsNilpotent.eq_zero ⟨exponent, hresidue⟩

theorem normal_p_central_residue_zero_of_outside_centralizer {G : Type*}
    [Group G] [Fintype G] (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    (prime : ℕ) [Fact prime.Prime] [CharP (ComplexAlgebraicIntegers ⧸ ideal) prime]
    (subgroup : Subgroup G) [subgroup.Normal] (hgroup : IsPGroup prime subgroup)
    (value : centralCoefficientSubring (G := G) (localizedComplexIntegerRing ideal))
    (hzero : ∀ element ∈ Subgroup.centralizer (subgroup : Set G), value.val.coeff element = 0)
    (label : basis.index) : centralCharacterResidueHom basis ideal label value = 0 := by
  let : Field (ComplexAlgebraicIntegers ⧸ ideal) := Ideal.Quotient.field ideal
  apply centralCharacterResidueHom_zero_of_reduction_nilpotent basis ideal value _ label
  apply normal_p_quotient_zero_element_nilpotent prime subgroup hgroup
  apply normal_p_invariant_quotient_zero_of_outside_centralizer prime subgroup hgroup
    (centralCoefficientReductionHom ideal value)
    (centralCoefficientReductionHom_conjugationInvariant ideal value subgroup)
  intro element hcentral
  simp only [centralCoefficientReductionHom, RingHom.comp_apply, MonoidAlgebra.coeff_mapRingHom,
    centralCoefficientLiftHom_coeff]
  have hcoefficient : (⟨value.val.coeff element, centralCoefficientSubring_coefficients _ value element⟩ :
      localizedComplexIntegerRing ideal) = 0 := Subtype.ext (hzero element hcentral)
  rw [hcoefficient, map_zero]

theorem normal_p_central_residue_determined_by_projection {G : Type*}
    [Group G] [Fintype G] (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    (prime : ℕ) [Fact prime.Prime] [CharP (ComplexAlgebraicIntegers ⧸ ideal) prime]
    (subgroup : Subgroup G) [subgroup.Normal] (hgroup : IsPGroup prime subgroup)
    (left right : centralCoefficientSubring (G := G) (localizedComplexIntegerRing ideal))
    (hequal : centralSubgroupCoefficientProjection (localizedComplexIntegerRing ideal)
      (Subgroup.centralizer (subgroup : Set G)) left =
        centralSubgroupCoefficientProjection (localizedComplexIntegerRing ideal)
          (Subgroup.centralizer (subgroup : Set G)) right)
    (label : basis.index) :
    centralCharacterResidueHom basis ideal label left = centralCharacterResidueHom basis ideal label right := by
  have hzero := normal_p_central_residue_zero_of_outside_centralizer basis ideal prime subgroup hgroup
    (left - right) (fun element hcentral => by
      have hcoefficient := congrArg (fun value => value.val.coeff
        (⟨element, hcentral⟩ : Subgroup.centralizer (subgroup : Set G))) hequal
      rw [centralSubgroupCoefficientProjection_val, centralSubgroupCoefficientProjection_val,
        subgroupCoefficientProjection_coeff, subgroupCoefficientProjection_coeff] at hcoefficient
      change (left.val - right.val).coeff element = 0
      rw [MonoidAlgebra.coeff_sub, Finsupp.sub_apply, hcoefficient, sub_self]) label
  rwa [map_sub, sub_eq_zero] at hzero

end CFSG.TwoRankLowerBound.Helpers
