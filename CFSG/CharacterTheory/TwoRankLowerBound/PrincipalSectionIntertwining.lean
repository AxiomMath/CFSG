module

public import CFSG.CharacterTheory.TwoRankLowerBound.BlockSectionOrthogonality
public import CFSG.CharacterTheory.TwoRankLowerBound.BrauerMismatchRestriction
public import CFSG.CharacterTheory.TwoRankLowerBound.PrincipalBrauerCorrespondence
public import CFSG.CharacterTheory.TwoRankLowerBound.CentralResidueNilpotence

public section

open scoped BigOperators Classical

namespace CFSG.TwoRankLowerBound.Helpers

theorem localized_residue_zero_iff_canonical (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    (value : localizedComplexIntegerRing ideal) :
    localizedComplexIntegerResidue ideal value = 0 ↔ IsLocalRing.residue (localizedComplexIntegerRing ideal) value = 0 := by
  rw [← not_iff_not, ← ne_eq, ← ne_eq, ← localizedComplexIntegerResidue_isUnit_iff,
    IsLocalRing.residue_ne_zero_iff_isUnit]

theorem localized_groupAlgebra_residue_zero_canonical {group : Type*} [Group group]
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    (value : MonoidAlgebra (localizedComplexIntegerRing ideal) group)
    (hzero : MonoidAlgebra.mapRingHom group (localizedComplexIntegerResidue ideal) value = 0) :
    MonoidAlgebra.mapRingHom group (IsLocalRing.residue (localizedComplexIntegerRing ideal)) value = 0 := by
  ext element
  rw [MonoidAlgebra.coeff_mapRingHom]
  apply (localized_residue_zero_iff_canonical ideal _).mp
  have hcoefficient := congrArg (fun algebraElement => algebraElement.coeff element) hzero
  simpa only [MonoidAlgebra.coeff_mapRingHom, MonoidAlgebra.coeff_zero, Finsupp.zero_apply] using hcoefficient

theorem centralCoefficientLiftHom_subgroup_projection {group : Type*} [Group group] [Fintype group]
    (ring : Subring ℂ) (subgroup : Subgroup group) (value : centralCoefficientSubring (G := group) ring) :
    centralCoefficientLiftHom ring (centralSubgroupCoefficientProjection ring subgroup value) =
      subgroupCoefficientProjection subgroup (centralCoefficientLiftHom ring value) := by
  ext element
  rw [centralCoefficientLiftHom_coeff, subgroupCoefficientProjection_coeff, centralCoefficientLiftHom_coeff]
  exact subgroupCoefficientProjection_coeff subgroup value.val element

set_option maxHeartbeats 1000000 in
theorem admissible_mismatch_section_projection_zero {group : Type*} [Group group] [Fintype group]
    (basis : FiniteIrreducibleCharacterBasis group)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    (prime : ℕ) [Fact prime.Prime] [CharP (ComplexAlgebraicIntegers ⧸ ideal) prime]
    (primary : group) (exponent : ℕ) (hprimary : orderOf primary ∣ prime ^ exponent)
    (localBasis : FiniteIrreducibleCharacterBasis (Subgroup.centralizer (Subgroup.zpowers primary : Set group)))
    (ambientSupport : Finset basis.index)
    (hambient : characterSubsetAdmissible basis (localizedComplexIntegerRing ideal) ambientSupport)
    (localSupport : Finset localBasis.index)
    (hlocal : characterSubsetAdmissible localBasis (localizedComplexIntegerRing ideal) localSupport)
    (hmismatch : ∀ localLabel ∈ localSupport,
      brauerNormalizerCharacterResidueHom ideal prime (Subgroup.zpowers primary)
        (IsPGroup.of_card_dvd_pow (n := exponent) (by rw [Nat.card_zpowers]; exact hprimary))
        (Subgroup.centralizer (Subgroup.zpowers primary : Set group)) le_rfl (Subgroup.centralizer_le_normalizer _)
        localBasis localLabel (admissibleCharacterSubsetElement basis _ ambientSupport hambient) = 0)
    (regular : Subgroup.centralizer (Subgroup.zpowers primary : Set group))
    (hregular : Nat.Coprime prime (orderOf regular.val)) (label : basis.index) (hlabel : label ∈ ambientSupport) :
    characterSubsetProjection localBasis localSupport (fun member => (basis.representation label).character member.val)
      ((⟨primary, element_mem_centralizer_zpowers primary⟩ :
        Subgroup.centralizer (Subgroup.zpowers primary : Set group)) * regular)⁻¹ = 0 := by
  let ring := localizedComplexIntegerRing ideal
  let := localizedComplexIntegerRing_residue_charP ideal prime
  have hgroup : IsPGroup prime (Subgroup.zpowers primary) :=
    IsPGroup.of_card_dvd_pow (by rw [Nat.card_zpowers]; exact hprimary)
  have hzero := centralCoefficientReductionHom_projection_block_mismatch_zero basis ideal prime
    (Subgroup.zpowers primary) hgroup localBasis ambientSupport hambient localSupport hlocal hmismatch
  change MonoidAlgebra.mapRingHom _ (localizedComplexIntegerResidue ideal)
    (centralCoefficientLiftHom ring
      (centralSubgroupCoefficientProjection ring (Subgroup.centralizer (Subgroup.zpowers primary : Set group))
        (admissibleCharacterSubsetElement basis ring ambientSupport hambient) *
          admissibleCharacterSubsetElement localBasis ring localSupport hlocal)) = 0 at hzero
  rw [map_mul, centralCoefficientLiftHom_subgroup_projection] at hzero
  exact admissible_mismatch_character_local_projection_zero ring prime basis ambientSupport hambient primary exponent
    hprimary localBasis localSupport hlocal regular hregular
      (rootOfUnity_mem_localizedComplexIntegerRing ideal)
      (localized_groupAlgebra_residue_zero_canonical ideal _ hzero) label hlabel

theorem principal_local_projection_zero_of_ambient_nonprincipal {group : Type*}
    [Group group] [Fintype group] (basis : FiniteIrreducibleCharacterBasis group)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    (prime : ℕ) [Fact prime.Prime] [CharP (ComplexAlgebraicIntegers ⧸ ideal) prime]
    (principal : basis.index) (hprincipal : (basis.representation principal).character = 1)
    (primary : group) (exponent : ℕ) (hprimary : orderOf primary ∣ prime ^ exponent)
    (localBasis : FiniteIrreducibleCharacterBasis (Subgroup.centralizer (Subgroup.zpowers primary : Set group)))
    (localPrincipal : localBasis.index) (hlocalPrincipal : (localBasis.representation localPrincipal).character = 1)
    (regular : Subgroup.centralizer (Subgroup.zpowers primary : Set group))
    (hregular : Nat.Coprime prime (orderOf regular.val)) (label : basis.index)
    (hlabel : label ∉ coefficientBlock basis (localizedComplexIntegerRing ideal) principal) :
    characterSubsetProjection localBasis (coefficientBlock localBasis (localizedComplexIntegerRing ideal) localPrincipal)
      (fun member => (basis.representation label).character member.val)
        ((⟨primary, element_mem_centralizer_zpowers primary⟩ :
          Subgroup.centralizer (Subgroup.zpowers primary : Set group)) * regular)⁻¹ = 0 := by
  let ambientSupport := (coefficientBlock basis (localizedComplexIntegerRing ideal) principal)ᶜ
  have hambient := characterSubsetAdmissible_compl basis (localizedComplexIntegerRing ideal) _
    (coefficientBlock_admissible basis (localizedComplexIntegerRing ideal) principal)
  apply admissible_mismatch_section_projection_zero basis ideal prime primary exponent hprimary localBasis
    ambientSupport hambient _ (coefficientBlock_admissible localBasis _ localPrincipal) _ regular hregular label
      (Finset.mem_compl.mpr hlabel)
  intro localLabel hmember
  have hgroup : IsPGroup prime (Subgroup.zpowers primary) :=
    IsPGroup.of_card_dvd_pow (by rw [Nat.card_zpowers]; exact hprimary)
  have hequal := (sameCoefficientBlock_iff_centralCharacterResidueHom_eq localBasis ideal localLabel localPrincipal).mp
    (sameCoefficientBlock_symm localBasis _ ((coefficientBlock_mem_iff _ _ _ _).mp hmember))
  have himage := brauerNormalizer_principal_residue_image basis ideal prime (Subgroup.zpowers primary) hgroup
    (Subgroup.centralizer (Subgroup.zpowers primary : Set group)) le_rfl (Subgroup.centralizer_le_normalizer _)
      localBasis principal hprincipal localPrincipal hlocalPrincipal
  change centralCharacterResidueHom localBasis ideal localLabel
    (centralNormalizerCoefficientProjection _ (Subgroup.zpowers primary) _ _ _ _) = 0
  rw [hequal]
  have hvalue := congrArg (fun hom => hom (admissibleCharacterSubsetElement basis _ ambientSupport hambient)) himage
  rw [centralCharacterResidueHom_subset, ite_eq_right (Finset.notMem_compl.mpr
    (coefficientBlock_self_mem basis _ principal))] at hvalue
  exact hvalue

theorem nonprincipal_local_projection_zero_of_ambient_principal {group : Type*}
    [Group group] [Fintype group] (basis : FiniteIrreducibleCharacterBasis group)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    (prime : ℕ) [Fact prime.Prime] [CharP (ComplexAlgebraicIntegers ⧸ ideal) prime]
    (principal : basis.index) (hprincipal : (basis.representation principal).character = 1)
    (primary : group) (exponent : ℕ) (hprimary : orderOf primary ∣ prime ^ exponent)
    (localBasis : FiniteIrreducibleCharacterBasis (Subgroup.centralizer (Subgroup.zpowers primary : Set group)))
    (localPrincipal : localBasis.index) (hlocalPrincipal : (localBasis.representation localPrincipal).character = 1)
    (regular : Subgroup.centralizer (Subgroup.zpowers primary : Set group))
    (hregular : Nat.Coprime prime (orderOf regular.val)) (label : basis.index)
    (hlabel : label ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal) :
    characterSubsetProjection localBasis (coefficientBlock localBasis (localizedComplexIntegerRing ideal) localPrincipal)ᶜ
      (fun member => (basis.representation label).character member.val)
        ((⟨primary, element_mem_centralizer_zpowers primary⟩ :
          Subgroup.centralizer (Subgroup.zpowers primary : Set group)) * regular)⁻¹ = 0 := by
  let ambientSupport := coefficientBlock basis (localizedComplexIntegerRing ideal) principal
  have hambient := coefficientBlock_admissible basis (localizedComplexIntegerRing ideal) principal
  have hlocal := characterSubsetAdmissible_compl localBasis (localizedComplexIntegerRing ideal) _
    (coefficientBlock_admissible localBasis (localizedComplexIntegerRing ideal) localPrincipal)
  apply admissible_mismatch_section_projection_zero basis ideal prime primary exponent hprimary localBasis
    ambientSupport hambient _ hlocal _ regular hregular label hlabel
  intro localLabel hmember
  have hgroup : IsPGroup prime (Subgroup.zpowers primary) :=
    IsPGroup.of_card_dvd_pow (by rw [Nat.card_zpowers]; exact hprimary)
  obtain ⟨ambientLabel, himage⟩ := brauerNormalizer_block_image_exists basis ideal prime
    (Subgroup.zpowers primary) hgroup (Subgroup.centralizer (Subgroup.zpowers primary : Set group)) le_rfl
      (Subgroup.centralizer_le_normalizer _) localBasis localLabel
  have hnot : ambientLabel ∉ ambientSupport := by
    intro hinside
    have hprincipalBlock := (brauerNormalizer_principal_block_iff basis ideal prime (Subgroup.zpowers primary) hgroup
      (Subgroup.centralizer (Subgroup.zpowers primary : Set group)) (Subgroup.le_centralizer_iff_isMulCommutative.mpr
        inferInstance) le_rfl (Subgroup.centralizer_le_normalizer _) localBasis principal hprincipal localPrincipal
          hlocalPrincipal localLabel ambientLabel himage).mp
            (sameCoefficientBlock_symm basis _ ((coefficientBlock_mem_iff _ _ _ _).mp hinside))
    exact (Finset.mem_compl.mp hmember) ((coefficientBlock_mem_iff _ _ _ _).mpr
      (sameCoefficientBlock_symm localBasis _ hprincipalBlock))
  have hvalue := congrArg (fun hom => hom (admissibleCharacterSubsetElement basis _ ambientSupport hambient)) himage
  rw [centralCharacterResidueHom_subset, ite_eq_right hnot] at hvalue
  exact hvalue

theorem characterSubsetProjection_character_not_mem {group : Type*} [Group group] [Fintype group]
    (basis : FiniteIrreducibleCharacterBasis group) (support : Finset basis.index)
    (label : basis.index) (hlabel : label ∉ support) :
    characterSubsetProjection basis support (basis.representation label).character = 0 := by
  change (∑ member ∈ support,
    characterPairing (basis.representation label).character (basis.representation member).character •
      (basis.representation member).character) = 0
  apply Finset.sum_eq_zero
  intro member hmember
  have hne : (basis.representation label).character ≠ (basis.representation member).character := by
    intro hequal
    have hindices : label = member := basis.distinct hequal
    exact hlabel (hindices ▸ hmember)
  rw [characterPairing_irreducible _ _ (basis.irreducible label) (basis.irreducible member),
    ite_eq_right hne, zero_smul]

theorem characterSubsetProjection_add_compl {group : Type*} [Group group] [Fintype group]
    (basis : FiniteIrreducibleCharacterBasis group) (support : Finset basis.index)
    (function : group → ℂ)
    (hclass : ∀ element conjugator : group,
      function (conjugator * element * conjugator⁻¹) = function element) :
    characterSubsetProjection basis support function + characterSubsetProjection basis supportᶜ function = function := by
  change (∑ label ∈ support, characterPairing function (basis.representation label).character •
    (basis.representation label).character) +
    (∑ label ∈ supportᶜ, characterPairing function (basis.representation label).character •
      (basis.representation label).character) = function
  rw [Finset.sum_add_sum_compl]
  funext element
  simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using
    (finiteIrreducibleCharacterBasis_reconstruction basis function hclass element).symm

theorem principal_local_section_projection_character {group : Type*}
    [Group group] [Fintype group] (basis : FiniteIrreducibleCharacterBasis group)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    (prime : ℕ) [Fact prime.Prime] [CharP (ComplexAlgebraicIntegers ⧸ ideal) prime]
    (principal : basis.index) (hprincipal : (basis.representation principal).character = 1)
    (primary : group) (exponent : ℕ) (hprimary : orderOf primary ∣ prime ^ exponent)
    (localBasis : FiniteIrreducibleCharacterBasis (Subgroup.centralizer (Subgroup.zpowers primary : Set group)))
    (localPrincipal : localBasis.index) (hlocalPrincipal : (localBasis.representation localPrincipal).character = 1)
    (regular : Subgroup.centralizer (Subgroup.zpowers primary : Set group))
    (hregular : Nat.Coprime prime (orderOf regular.val)) (label : basis.index) :
    characterSubsetProjection localBasis (coefficientBlock localBasis (localizedComplexIntegerRing ideal) localPrincipal)
      (fun member => (basis.representation label).character member.val)
        ((⟨primary, element_mem_centralizer_zpowers primary⟩ :
          Subgroup.centralizer (Subgroup.zpowers primary : Set group)) * regular)⁻¹ =
    characterSubsetProjection basis (coefficientBlock basis (localizedComplexIntegerRing ideal) principal)
      (basis.representation label).character
        (((⟨primary, element_mem_centralizer_zpowers primary⟩ :
          Subgroup.centralizer (Subgroup.zpowers primary : Set group)) * regular)⁻¹).val := by
  by_cases hlabel : label ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal
  · rw [characterSubsetProjection_character basis _ label hlabel]
    have hzero := nonprincipal_local_projection_zero_of_ambient_principal basis ideal prime principal hprincipal
      primary exponent hprimary localBasis localPrincipal hlocalPrincipal regular hregular label hlabel
    have hsum := congrFun (characterSubsetProjection_add_compl localBasis
      (coefficientBlock localBasis (localizedComplexIntegerRing ideal) localPrincipal)
      (fun member => (basis.representation label).character member.val)
      (by intro element conjugator; exact Representation.char_conj _ element.val conjugator.val))
        ((⟨primary, element_mem_centralizer_zpowers primary⟩ :
          Subgroup.centralizer (Subgroup.zpowers primary : Set group)) * regular)⁻¹
    simpa only [Pi.add_apply, hzero, add_zero] using hsum
  · rw [characterSubsetProjection_character_not_mem basis _ label hlabel]
    exact principal_local_projection_zero_of_ambient_nonprincipal basis ideal prime principal hprincipal
      primary exponent hprimary localBasis localPrincipal hlocalPrincipal regular hregular label hlabel

theorem principal_local_section_projection {group : Type*}
    [Group group] [Fintype group] (basis : FiniteIrreducibleCharacterBasis group)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    (prime : ℕ) [Fact prime.Prime] [CharP (ComplexAlgebraicIntegers ⧸ ideal) prime]
    (principal : basis.index) (hprincipal : (basis.representation principal).character = 1)
    (primary : group) (exponent : ℕ) (hprimary : orderOf primary ∣ prime ^ exponent)
    (localBasis : FiniteIrreducibleCharacterBasis (Subgroup.centralizer (Subgroup.zpowers primary : Set group)))
    (localPrincipal : localBasis.index) (hlocalPrincipal : (localBasis.representation localPrincipal).character = 1)
    (regular : Subgroup.centralizer (Subgroup.zpowers primary : Set group))
    (hregular : Nat.Coprime prime (orderOf regular.val))
    (function : group → ℂ)
    (hclass : ∀ element conjugator : group,
      function (conjugator * element * conjugator⁻¹) = function element) :
    characterSubsetProjection localBasis (coefficientBlock localBasis (localizedComplexIntegerRing ideal) localPrincipal)
      (fun member => function member.val)
        ((⟨primary, element_mem_centralizer_zpowers primary⟩ :
          Subgroup.centralizer (Subgroup.zpowers primary : Set group)) * regular)⁻¹ =
    characterSubsetProjection basis (coefficientBlock basis (localizedComplexIntegerRing ideal) principal) function
        (((⟨primary, element_mem_centralizer_zpowers primary⟩ :
          Subgroup.centralizer (Subgroup.zpowers primary : Set group)) * regular)⁻¹).val := by
  let restriction : (group → ℂ) →ₗ[ℂ]
      (Subgroup.centralizer (Subgroup.zpowers primary : Set group) → ℂ) :=
    LinearMap.pi fun member => LinearMap.proj member.val
  let sectionPoint := ((⟨primary, element_mem_centralizer_zpowers primary⟩ :
    Subgroup.centralizer (Subgroup.zpowers primary : Set group)) * regular)⁻¹
  let localEvaluation : (group → ℂ) →ₗ[ℂ] ℂ :=
    (LinearMap.proj sectionPoint).comp
      ((characterSubsetProjection localBasis
        (coefficientBlock localBasis (localizedComplexIntegerRing ideal) localPrincipal)).comp restriction)
  let ambientEvaluation : (group → ℂ) →ₗ[ℂ] ℂ :=
    (LinearMap.proj sectionPoint.val).comp
      (characterSubsetProjection basis (coefficientBlock basis (localizedComplexIntegerRing ideal) principal))
  change localEvaluation function = ambientEvaluation function
  have hexpansion : function = ∑ label, characterPairing function (basis.representation label).character •
      (basis.representation label).character := by
    funext element
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using
      finiteIrreducibleCharacterBasis_reconstruction basis function hclass element
  rw [hexpansion, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro label _
  rw [map_smul, map_smul]
  congr 1
  exact principal_local_section_projection_character basis ideal prime principal hprincipal primary exponent hprimary
    localBasis localPrincipal hlocalPrincipal regular hregular label

end CFSG.TwoRankLowerBound.Helpers
