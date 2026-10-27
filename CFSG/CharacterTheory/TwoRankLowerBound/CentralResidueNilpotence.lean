module

public import CFSG.CharacterTheory.TwoRankLowerBound.LocalBlockExistence

public section

open scoped BigOperators Classical

namespace CFSG.TwoRankLowerBound.Helpers

@[expose, instance_reducible] noncomputable def ringHom_range_commRing {source target : Type*}
    [CommRing source] [Ring target] (hom : source →+* target) : CommRing hom.range :=
  { (inferInstance : Ring hom.range) with
    mul_comm := by
      intro left right
      obtain ⟨leftPreimage, hleft⟩ := left.property
      obtain ⟨rightPreimage, hright⟩ := right.property
      apply Subtype.ext
      change left.val * right.val = right.val * left.val
      rw [← hleft, ← hright, ← map_mul, ← map_mul, mul_comm] }

theorem centralCoefficientReductionHom_nilpotent_of_residues_zero {group : Type*}
    [Group group] [Fintype group] (basis : FiniteIrreducibleCharacterBasis group)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    (value : centralCoefficientSubring (G := group) (localizedComplexIntegerRing ideal))
    (hzero : ∀ label, centralCharacterResidueHom basis ideal label value = 0) :
    IsNilpotent (centralCoefficientReductionHom ideal value) := by
  let scalar := fun label => localCentralCharacterHom basis ideal label value
  have hannihilates : (∏ label : basis.index,
      (value - centralCoefficientScalarHom (localizedComplexIntegerRing ideal) (scalar label))) = 0 := by
    apply localCentralCharacterHom_separates basis ideal
    intro label
    rw [map_prod, map_zero]
    apply Finset.prod_eq_zero (Finset.mem_univ label)
    rw [map_sub, localCentralCharacterHom_scalar, sub_self]
  let reduction := centralCoefficientReductionHom (G := group) ideal
  let : CommRing reduction.range := ringHom_range_commRing reduction
  have hreduced := congrArg reduction.rangeRestrict hannihilates
  rw [map_prod, map_zero] at hreduced
  have hfactor : ∀ label : basis.index,
      reduction.rangeRestrict
        (value - centralCoefficientScalarHom (localizedComplexIntegerRing ideal) (scalar label)) =
          reduction.rangeRestrict value := by
    intro label
    apply Subtype.ext
    change centralCoefficientReductionHom ideal
      (value - centralCoefficientScalarHom (localizedComplexIntegerRing ideal) (scalar label)) =
        centralCoefficientReductionHom ideal value
    rw [map_sub, centralCoefficientReductionHom_scalar]
    have hscalar : localizedComplexIntegerResidue ideal (scalar label) = 0 := hzero label
    rw [hscalar, MonoidAlgebra.single_zero, sub_zero]
  simp only [hfactor, Finset.prod_const, Finset.card_univ] at hreduced
  exact ⟨Fintype.card basis.index, congrArg Subtype.val hreduced⟩

theorem centralCoefficientReductionHom_idempotent_zero_of_residues_zero {group : Type*}
    [Group group] [Fintype group] (basis : FiniteIrreducibleCharacterBasis group)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    (value : centralCoefficientSubring (G := group) (localizedComplexIntegerRing ideal))
    (hidempotent : IsIdempotentElem (centralCoefficientReductionHom ideal value))
    (hzero : ∀ label, centralCharacterResidueHom basis ideal label value = 0) :
    centralCoefficientReductionHom ideal value = 0 :=
  hidempotent.eq_zero_of_isNilpotent
    (centralCoefficientReductionHom_nilpotent_of_residues_zero basis ideal value hzero)

theorem centralCoefficientReductionHom_projection_block_mismatch_zero {group : Type*}
    [Group group] [Fintype group] (basis : FiniteIrreducibleCharacterBasis group)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    (prime : ℕ) [Fact prime.Prime] [CharP (ComplexAlgebraicIntegers ⧸ ideal) prime]
    (primary : Subgroup group) (hprimary : IsPGroup prime primary)
    (localBasis : FiniteIrreducibleCharacterBasis (Subgroup.centralizer (primary : Set group)))
    (ambientSupport : Finset basis.index)
    (hambient : characterSubsetAdmissible basis (localizedComplexIntegerRing ideal) ambientSupport)
    (localSupport : Finset localBasis.index)
    (hlocal : characterSubsetAdmissible localBasis (localizedComplexIntegerRing ideal) localSupport)
    (hmismatch : ∀ localLabel ∈ localSupport,
      brauerNormalizerCharacterResidueHom ideal prime primary hprimary (Subgroup.centralizer (primary : Set group))
        le_rfl (Subgroup.centralizer_le_normalizer _) localBasis localLabel
          (admissibleCharacterSubsetElement basis _ ambientSupport hambient) = 0) :
    centralCoefficientReductionHom ideal
      (centralSubgroupCoefficientProjection _ (Subgroup.centralizer (primary : Set group))
        (admissibleCharacterSubsetElement basis _ ambientSupport hambient) *
          admissibleCharacterSubsetElement localBasis _ localSupport hlocal) = 0 := by
  let ambient := admissibleCharacterSubsetElement basis (localizedComplexIntegerRing ideal) ambientSupport hambient
  let localElement := admissibleCharacterSubsetElement localBasis (localizedComplexIntegerRing ideal) localSupport hlocal
  let projection := centralSubgroupCoefficientProjection (localizedComplexIntegerRing ideal)
    (Subgroup.centralizer (primary : Set group))
  have hprojection : centralNormalizerCoefficientProjection _ primary (Subgroup.centralizer (primary : Set group))
      le_rfl (Subgroup.centralizer_le_normalizer _) ambient = projection ambient := by
    apply Subtype.ext
    ext element
    rw [centralNormalizerCoefficientProjection_coeff, ite_eq_left element.property]
    exact (subgroupCoefficientProjection_coeff _ ambient.val element).symm
  have hidempotent : IsIdempotentElem (centralCoefficientReductionHom ideal (projection ambient)) := by
    have hleft : IsIdempotentElem ambient :=
      Subtype.ext (characterSubsetIdempotent_isIdempotent basis ambientSupport).eq
    have hmap := hleft.map (reducedBrauerProjectionHom ideal prime primary hprimary
      (Subgroup.centralizer (primary : Set group)) le_rfl (Subgroup.centralizer_le_normalizer _))
    change IsIdempotentElem (centralCoefficientReductionHom ideal
      (centralNormalizerCoefficientProjection _ primary (Subgroup.centralizer (primary : Set group))
        le_rfl (Subgroup.centralizer_le_normalizer _) ambient)) at hmap
    rwa [hprojection] at hmap
  have hlocalIdempotent : IsIdempotentElem (centralCoefficientReductionHom ideal localElement) :=
    (show IsIdempotentElem localElement from
      Subtype.ext (characterSubsetIdempotent_isIdempotent localBasis localSupport).eq).map _
  apply centralCoefficientReductionHom_idempotent_zero_of_residues_zero localBasis ideal
    (projection ambient * localElement)
  · rw [map_mul]
    exact hidempotent.mul_of_commute
      ((Commute.all (projection ambient) localElement).map (centralCoefficientReductionHom ideal)) hlocalIdempotent
  · intro label
    rw [map_mul, centralCharacterResidueHom_subset]
    by_cases hmember : label ∈ localSupport
    · rw [ite_eq_left hmember, mul_one]
      have hequal := hmismatch label hmember
      change centralCharacterResidueHom localBasis ideal label
        (centralNormalizerCoefficientProjection _ primary (Subgroup.centralizer (primary : Set group))
          le_rfl (Subgroup.centralizer_le_normalizer _) ambient) = 0 at hequal
      rwa [hprojection] at hequal
    · rw [ite_eq_right hmember, mul_zero]

end CFSG.TwoRankLowerBound.Helpers
