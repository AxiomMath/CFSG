module

public import CFSG.CharacterTheory.TwoRankLowerBound.BrauerPrincipalCorner
public import CFSG.CharacterTheory.TwoRankLowerBound.CentralCharacterResidueCriterion
public import CFSG.CharacterTheory.TwoRankLowerBound.CentralNormalizerProjection

public section

open scoped BigOperators Classical

namespace CFSG.TwoRankLowerBound.Helpers

theorem centralCharacterScalar_principal {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1)
    (value : MonoidAlgebra ℂ G) :
    centralCharacterScalar basis value principal = groupAlgebraAugmentation ℂ G value := by
  unfold centralCharacterScalar
  rw [hprincipal, characterPairing, groupAlgebraAugmentation_sum]
  simp only [Pi.one_apply, mul_one, div_one]
  rw [← mul_assoc, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr Nat.card_pos.ne'), one_mul]
  exact Equiv.sum_comp (Equiv.inv G) value.coeff

theorem localCentralCharacterHom_principal {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsPrime]
    (principal : basis.index) (hprincipal : (basis.representation principal).character = 1)
    (value : centralCoefficientSubring (G := G) (localizedComplexIntegerRing ideal)) :
    localCentralCharacterHom basis ideal principal value =
      groupAlgebraAugmentation (localizedComplexIntegerRing ideal) G
        (centralCoefficientLiftHom _ value) := by
  apply Subtype.ext
  rw [localCentralCharacterHom_coe, centralCharacterScalar_principal basis principal hprincipal]
  have hequal := groupAlgebraAugmentation_map (localizedComplexIntegerRing ideal).subtype
    (centralCoefficientLiftHom _ value)
  rw [centralCoefficientLiftHom_map] at hequal
  exact hequal

theorem centralCharacterResidueHom_principal {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    (principal : basis.index) (hprincipal : (basis.representation principal).character = 1)
    (value : centralCoefficientSubring (G := G) (localizedComplexIntegerRing ideal)) :
    centralCharacterResidueHom basis ideal principal value =
      groupAlgebraAugmentation (ComplexAlgebraicIntegers ⧸ ideal) G
        (centralCoefficientReductionHom ideal value) := by
  change localizedComplexIntegerResidue ideal (localCentralCharacterHom basis ideal principal value) = _
  rw [localCentralCharacterHom_principal basis ideal principal hprincipal]
  exact (groupAlgebraAugmentation_map (localizedComplexIntegerResidue ideal)
    (centralCoefficientLiftHom _ value)).symm

theorem normalizerCentralizerCoefficientProjection_augmentation {ring G : Type*}
    [CommRing ring] [Group G] [Fintype G] (subgroup intermediate : Subgroup G)
    (hcontains : Subgroup.centralizer (subgroup : Set G) ≤ intermediate)
    (value : MonoidAlgebra ring G) :
    groupAlgebraAugmentation ring intermediate
      (normalizerCentralizerCoefficientProjection subgroup intermediate hcontains value) =
      groupAlgebraAugmentation ring (Subgroup.centralizer (subgroup : Set G))
        (subgroupCoefficientProjection (Subgroup.centralizer (subgroup : Set G)) value) := by
  rw [groupAlgebraAugmentation_sum, groupAlgebraAugmentation_sum]
  simp only [normalizerCentralizerCoefficientProjection_coeff, subgroupCoefficientProjection_coeff]
  rw [← Finset.sum_filter]
  let equivalence : Subgroup.centralizer (subgroup : Set G) ≃
      {element : intermediate // element.val ∈ Subgroup.centralizer (subgroup : Set G)} :=
    { toFun member := ⟨⟨member.val, hcontains member.property⟩, member.property⟩
      invFun member := ⟨member.val.val, member.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Finset.sum_subtype (p := fun element : intermediate =>
    element.val ∈ Subgroup.centralizer (subgroup : Set G)) _ (fun element => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and])]
  exact (equivalence.sum_comp (fun member => value.coeff member.val.val)).symm

theorem brauerNormalizer_principal_residue_image {G : Type*}
    [Group G] [Fintype G] (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    (prime : ℕ) [Fact prime.Prime] [CharP (ComplexAlgebraicIntegers ⧸ ideal) prime]
    (subgroup : Subgroup G) (hgroup : IsPGroup prime subgroup) (intermediate : Subgroup G)
    (hcontains : Subgroup.centralizer (subgroup : Set G) ≤ intermediate)
    (hnormalizes : intermediate ≤ Subgroup.normalizer (subgroup : Set G))
    (localBasis : FiniteIrreducibleCharacterBasis intermediate)
    (principal : basis.index) (hprincipal : (basis.representation principal).character = 1)
    (localPrincipal : localBasis.index)
    (hlocalPrincipal : (localBasis.representation localPrincipal).character = 1) :
    brauerNormalizerCharacterResidueHom ideal prime subgroup hgroup intermediate hcontains hnormalizes
      localBasis localPrincipal = centralCharacterResidueHom basis ideal principal := by
  let : Field (ComplexAlgebraicIntegers ⧸ ideal) := Ideal.Quotient.field ideal
  apply RingHom.ext
  intro value
  change centralCharacterResidueHom localBasis ideal localPrincipal
    (centralNormalizerCoefficientProjection _ subgroup intermediate hcontains hnormalizes value) = _
  rw [centralCharacterResidueHom_principal localBasis ideal localPrincipal hlocalPrincipal,
    centralNormalizerCoefficientProjection_reduction, normalizerCentralizerCoefficientProjection_augmentation,
    centralCharacterResidueHom_principal basis ideal principal hprincipal]
  exact p_centralizer_projection_augmentation prime subgroup hgroup _
    (centralCoefficientReductionHom_conjugationInvariant ideal value subgroup)

theorem brauerNormalizer_principal_block_image {G : Type*}
    [Group G] [Fintype G] (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    (prime : ℕ) [Fact prime.Prime] [CharP (ComplexAlgebraicIntegers ⧸ ideal) prime]
    (subgroup : Subgroup G) (hgroup : IsPGroup prime subgroup) (intermediate : Subgroup G)
    (hcontains : Subgroup.centralizer (subgroup : Set G) ≤ intermediate)
    (hnormalizes : intermediate ≤ Subgroup.normalizer (subgroup : Set G))
    (localBasis : FiniteIrreducibleCharacterBasis intermediate)
    (principal : basis.index) (hprincipal : (basis.representation principal).character = 1)
    (localPrincipal : localBasis.index)
    (hlocalPrincipal : (localBasis.representation localPrincipal).character = 1)
    (imageLabel : basis.index)
    (himage : brauerNormalizerCharacterResidueHom ideal prime subgroup hgroup intermediate hcontains
      hnormalizes localBasis localPrincipal = centralCharacterResidueHom basis ideal imageLabel) :
    imageLabel ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal := by
  apply (coefficientBlock_mem_iff _ _ _ _).mpr
  apply (sameCoefficientBlock_iff_centralCharacterResidueHom_eq basis ideal principal imageLabel).mpr
  exact (brauerNormalizer_principal_residue_image basis ideal prime subgroup hgroup intermediate hcontains
    hnormalizes localBasis principal hprincipal localPrincipal hlocalPrincipal).symm.trans himage

end CFSG.TwoRankLowerBound.Helpers
