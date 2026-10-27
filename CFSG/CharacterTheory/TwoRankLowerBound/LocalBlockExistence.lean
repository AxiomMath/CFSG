module

public import CFSG.CharacterTheory.TwoRankLowerBound.NormalPBlockDefect
public import CFSG.CharacterTheory.TwoRankLowerBound.CentralSubalgebraResidueExtension

public section

open scoped BigOperators Classical

namespace CFSG.TwoRankLowerBound.Helpers

theorem centralCoefficientReductionHom_scalar {group : Type*} [Group group] [Fintype group]
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    (scalar : localizedComplexIntegerRing ideal) :
    centralCoefficientReductionHom (G := group) ideal (centralCoefficientScalarHom _ scalar) =
      MonoidAlgebra.single 1 (localizedComplexIntegerResidue ideal scalar) := by
  change MonoidAlgebra.mapRingHom group (localizedComplexIntegerResidue ideal)
    (centralCoefficientLiftHom _ (centralCoefficientScalarHom _ scalar)) = _
  have hscalar := congrArg (fun hom => hom scalar) (centralCoefficientLiftHom_scalar (G := group) _)
  change centralCoefficientLiftHom _ (centralCoefficientScalarHom _ scalar) =
    MonoidAlgebra.single 1 scalar at hscalar
  rw [hscalar, MonoidAlgebra.mapRingHom_single]

@[expose] noncomputable def reducedBrauerProjectionHom {group : Type*} [Group group] [Fintype group]
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    (prime : ℕ) [Fact prime.Prime] [CharP (ComplexAlgebraicIntegers ⧸ ideal) prime]
    (primary : Subgroup group) (hprimary : IsPGroup prime primary) (intermediate : Subgroup group)
    (hcontains : Subgroup.centralizer (primary : Set group) ≤ intermediate)
    (hnormalizes : intermediate ≤ Subgroup.normalizer (primary : Set group)) :
    centralCoefficientSubring (G := group) (localizedComplexIntegerRing ideal) →+*
      MonoidAlgebra (ComplexAlgebraicIntegers ⧸ ideal) intermediate where
  toFun value := centralCoefficientReductionHom ideal
    (centralNormalizerCoefficientProjection _ primary intermediate hcontains hnormalizes value)
  map_one' := by rw [centralNormalizerCoefficientProjection_one, map_one]
  map_zero' := by rw [map_zero, map_zero]
  map_add' left right := by rw [map_add, map_add]
  map_mul' left right := by
    rw [centralNormalizerCoefficientProjection_reduction, map_mul,
      normalizerCentralizerCoefficientProjection_mul prime primary hprimary intermediate hcontains _ _
        (centralCoefficientReductionHom_conjugationInvariant ideal left primary)
        (centralCoefficientReductionHom_conjugationInvariant ideal right primary),
      ← centralNormalizerCoefficientProjection_reduction,
      ← centralNormalizerCoefficientProjection_reduction]

theorem reducedBrauerProjectionHom_coeff {group : Type*} [Group group] [Fintype group]
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    (prime : ℕ) [Fact prime.Prime] [CharP (ComplexAlgebraicIntegers ⧸ ideal) prime]
    (primary : Subgroup group) (hprimary : IsPGroup prime primary) (intermediate : Subgroup group)
    (hcontains : Subgroup.centralizer (primary : Set group) ≤ intermediate)
    (hnormalizes : intermediate ≤ Subgroup.normalizer (primary : Set group))
    (value : centralCoefficientSubring (G := group) (localizedComplexIntegerRing ideal)) (element : intermediate) :
    (reducedBrauerProjectionHom ideal prime primary hprimary intermediate hcontains hnormalizes value).coeff
      element = if element.val ∈ Subgroup.centralizer (primary : Set group) then
        localizedComplexIntegerResidue ideal
          ⟨value.val.coeff element.val, centralCoefficientSubring_coefficients _ value element.val⟩ else 0 := by
  change (centralCoefficientReductionHom ideal
    (centralNormalizerCoefficientProjection _ primary intermediate hcontains hnormalizes value)).coeff element = _
  rw [centralNormalizerCoefficientProjection_reduction, normalizerCentralizerCoefficientProjection_coeff]
  simp only [centralCoefficientReductionHom, RingHom.comp_apply, MonoidAlgebra.coeff_mapRingHom,
    centralCoefficientLiftHom_coeff]

theorem reducedBrauerProjectionHom_scalar {group : Type*} [Group group] [Fintype group]
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    (prime : ℕ) [Fact prime.Prime] [CharP (ComplexAlgebraicIntegers ⧸ ideal) prime]
    (primary : Subgroup group) (hprimary : IsPGroup prime primary) (intermediate : Subgroup group)
    (hcontains : Subgroup.centralizer (primary : Set group) ≤ intermediate)
    (hnormalizes : intermediate ≤ Subgroup.normalizer (primary : Set group))
    (scalar : localizedComplexIntegerRing ideal) :
    reducedBrauerProjectionHom ideal prime primary hprimary intermediate hcontains hnormalizes
      (centralCoefficientScalarHom _ scalar) =
        centralCoefficientReductionHom ideal (centralCoefficientScalarHom _ scalar) := by
  change centralCoefficientReductionHom ideal
    (centralNormalizerCoefficientProjection _ primary intermediate hcontains hnormalizes
      (centralCoefficientScalarHom _ scalar)) = _
  rw [centralNormalizerCoefficientProjection_scalar]

theorem central_class_coefficient_eq_at_member {group : Type*} [Group group] [Fintype group]
    (ring : Subring ℂ) (value : centralCoefficientSubring (G := group) ring)
    {conjugacyClass : ConjClasses group} {element : group}
    (hclass : ConjClasses.mk element = conjugacyClass) :
    centralConjugacyClassCoefficient ring value conjugacyClass =
      ⟨value.val.coeff element, centralCoefficientSubring_coefficients ring value element⟩ := by
  apply Subtype.ext
  rw [← hclass]
  exact central_groupAlgebra_coeff_class ring value element

theorem reducedBrauerProjectionHom_kernel_le_residue_kernel {group : Type*}
    [Group group] [Fintype group] (basis : FiniteIrreducibleCharacterBasis group)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    (prime : ℕ) [Fact prime.Prime] [CharP (ComplexAlgebraicIntegers ⧸ ideal) prime]
    (primary : Subgroup group) (hprimary : IsPGroup prime primary) (intermediate : Subgroup group)
    (hcontains : Subgroup.centralizer (primary : Set group) ≤ intermediate)
    (hnormalizes : intermediate ≤ Subgroup.normalizer (primary : Set group))
    {label : basis.index} {defect : Subgroup group}
    (hdefect : coefficientBlockDefect basis ideal prime label defect)
    (hsubconjugate : subgroupSubconjugate primary defect) :
    RingHom.ker (reducedBrauerProjectionHom ideal prime primary hprimary intermediate hcontains hnormalizes) ≤
      RingHom.ker (centralCharacterResidueHom basis ideal label) := by
  let : Fintype (ConjClasses group) := Fintype.ofFinite _
  intro value hzero
  rw [RingHom.mem_ker] at hzero ⊢
  rw [centralCharacterResidueHom_class_expansion]
  apply Finset.sum_eq_zero
  intro conjugacyClass _
  by_cases hvalue : centralCharacterResidueHom basis ideal label (centralConjugacyClassSum _ conjugacyClass) = 0
  · rw [hvalue, mul_zero]
  · obtain ⟨classPrimary, hclassPrimary⟩ := classDefect_exists prime conjugacyClass
    have hcontainsDefect := hdefect.2 conjugacyClass classPrimary hclassPrimary hvalue
    obtain ⟨element, hclass, hcentralizes⟩ :=
      (class_meets_centralizer_iff_subconjugate prime primary hprimary hclassPrimary).mpr
        (subgroupSubconjugate_trans hsubconjugate hcontainsDefect)
    have hcoefficient := congrArg (fun algebraElement => algebraElement.coeff
      (⟨element, hcontains hcentralizes⟩ : intermediate)) hzero
    rw [reducedBrauerProjectionHom_coeff, ite_eq_left hcentralizes] at hcoefficient
    rw [central_class_coefficient_eq_at_member _ value hclass, hcoefficient]
    simp

theorem residue_extension_through_reduced_projection {source target coefficient residue algebra : Type*}
    [CommRing source] [CommRing target] [CommRing coefficient] [CommRing residue] [Ring algebra]
    (projection : source →+* algebra) (targetReduction : target →+* algebra)
    (sourceScalar : coefficient →+* source) (targetScalar : coefficient →+* target)
    (scalarReduction : coefficient →+* residue) (residueHom : source →+* residue)
    (hscalar : ∀ scalar, residueHom (sourceScalar scalar) = scalarReduction scalar)
    (hprojectionScalar : ∀ scalar, projection (sourceScalar scalar) = targetReduction (targetScalar scalar))
    (hkernel : RingHom.ker projection ≤ RingHom.ker residueHom) :
    ∃ (subalgebra : Subring target) (hom : subalgebra →+* residue),
      (∀ scalar, targetScalar scalar ∈ subalgebra) ∧
      (∀ (scalar) (hmember : targetScalar scalar ∈ subalgebra),
        hom ⟨targetScalar scalar, hmember⟩ = scalarReduction scalar) ∧
      (∀ (value : source) (image : target), targetReduction image = projection value →
        ∃ hmember : image ∈ subalgebra, hom ⟨image, hmember⟩ = residueHom value) := by
  let rangeProjection := projection.rangeRestrict
  have hkernel' : RingHom.ker rangeProjection ≤ RingHom.ker residueHom := by
    intro value hvalue
    apply hkernel
    apply RingHom.mem_ker.mpr
    exact congrArg Subtype.val (RingHom.mem_ker.mp hvalue)
  let factor : projection.range →+* residue :=
    rangeProjection.liftOfSurjective projection.rangeRestrict_surjective ⟨residueHom, hkernel'⟩
  have hfactor : ∀ value, factor (rangeProjection value) = residueHom value :=
    RingHom.liftOfSurjective_comp_apply _ _ _
  let subalgebra := projection.range.comap targetReduction
  let reduction : subalgebra →+* projection.range :=
    (targetReduction.comp subalgebra.subtype).codRestrict projection.range (fun value => value.property)
  refine ⟨subalgebra, factor.comp reduction, ?_, ?_, ?_⟩
  · intro scalar
    exact ⟨sourceScalar scalar, hprojectionScalar scalar⟩
  · intro scalar hmember
    change factor (reduction ⟨targetScalar scalar, hmember⟩) = _
    have hequal : reduction ⟨targetScalar scalar, hmember⟩ = rangeProjection (sourceScalar scalar) :=
      Subtype.ext (hprojectionScalar scalar).symm
    rw [hequal, hfactor, hscalar]
  · intro value image hequal
    have hmember : image ∈ subalgebra := ⟨value, hequal.symm⟩
    refine ⟨hmember, ?_⟩
    change factor (reduction ⟨image, hmember⟩) = _
    have hresult : reduction ⟨image, hmember⟩ = rangeProjection value := Subtype.ext hequal
    rw [hresult, hfactor]

theorem brauerNormalizer_local_block_exists_of_subconjugate {group : Type*}
    [Group group] [Fintype group] (basis : FiniteIrreducibleCharacterBasis group)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    (prime : ℕ) [Fact prime.Prime] [CharP (ComplexAlgebraicIntegers ⧸ ideal) prime]
    (primary : Subgroup group) (hprimary : IsPGroup prime primary) (intermediate : Subgroup group)
    (hcontains : Subgroup.centralizer (primary : Set group) ≤ intermediate)
    (hnormalizes : intermediate ≤ Subgroup.normalizer (primary : Set group))
    (localBasis : FiniteIrreducibleCharacterBasis intermediate)
    {label : basis.index} {defect : Subgroup group}
    (hdefect : coefficientBlockDefect basis ideal prime label defect)
    (hsubconjugate : subgroupSubconjugate primary defect) :
    ∃ localLabel : localBasis.index,
      brauerNormalizerCharacterResidueHom ideal prime primary hprimary intermediate hcontains hnormalizes
        localBasis localLabel = centralCharacterResidueHom basis ideal label := by
  obtain ⟨subalgebra, hom, hcontainsScalar, hscalar, hfactor⟩ :=
    residue_extension_through_reduced_projection
      (reducedBrauerProjectionHom ideal prime primary hprimary intermediate hcontains hnormalizes)
      (centralCoefficientReductionHom (G := intermediate) ideal)
      (centralCoefficientScalarHom (G := group) (localizedComplexIntegerRing ideal))
      (centralCoefficientScalarHom (G := intermediate) (localizedComplexIntegerRing ideal))
      (localizedComplexIntegerResidue ideal) (centralCharacterResidueHom basis ideal label)
      (centralCharacterResidueHom_scalar basis ideal label)
      (reducedBrauerProjectionHom_scalar ideal prime primary hprimary intermediate hcontains hnormalizes)
      (reducedBrauerProjectionHom_kernel_le_residue_kernel basis ideal prime primary hprimary
        intermediate hcontains hnormalizes hdefect hsubconjugate)
  obtain ⟨localLabel, hequal⟩ := centralSubalgebraResidue_extension localBasis ideal subalgebra
    hcontainsScalar hom (fun scalar => hscalar scalar (hcontainsScalar scalar))
  refine ⟨localLabel, ?_⟩
  apply RingHom.ext
  intro value
  obtain ⟨hmember, hvalue⟩ := hfactor value
    (centralNormalizerCoefficientProjection _ primary intermediate hcontains hnormalizes value) rfl
  have hhom := congrArg (fun result => result
    ⟨centralNormalizerCoefficientProjection _ primary intermediate hcontains hnormalizes value, hmember⟩) hequal
  exact hhom.symm.trans hvalue

theorem brauerNormalizer_subconjugate_of_local_block_exists {group : Type*}
    [Group group] [Fintype group] (basis : FiniteIrreducibleCharacterBasis group)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    (prime : ℕ) [Fact prime.Prime] [CharP (ComplexAlgebraicIntegers ⧸ ideal) prime]
    (primary : Subgroup group) (hprimary : IsPGroup prime primary) (intermediate : Subgroup group)
    (hcontains : Subgroup.centralizer (primary : Set group) ≤ intermediate)
    (hnormalizes : intermediate ≤ Subgroup.normalizer (primary : Set group))
    (localBasis : FiniteIrreducibleCharacterBasis intermediate)
    {label : basis.index} {defect : Subgroup group}
    (hdefect : coefficientBlockDefect basis ideal prime label defect)
    (hexists : ∃ localLabel : localBasis.index,
      brauerNormalizerCharacterResidueHom ideal prime primary hprimary intermediate hcontains hnormalizes
        localBasis localLabel = centralCharacterResidueHom basis ideal label) :
    subgroupSubconjugate primary defect := by
  obtain ⟨localLabel, hequal⟩ := hexists
  obtain ⟨conjugacyClass, hclass, hvalue⟩ := hdefect.1
  apply (class_meets_centralizer_iff_subconjugate prime primary hprimary hclass).mp
  by_contra hnone
  have hprojection : centralNormalizerCoefficientProjection _ primary intermediate hcontains hnormalizes
      (centralConjugacyClassSum (localizedComplexIntegerRing ideal) conjugacyClass) = 0 := by
    apply Subtype.ext
    ext element
    rw [centralNormalizerCoefficientProjection_coeff]
    change (if element.val ∈ Subgroup.centralizer (primary : Set group) then
      (conjugacyClassSum (ring := ℂ) conjugacyClass).coeff element.val else 0) = 0
    rw [conjugacyClassSum_coeff]
    by_cases hcentralizes : element.val ∈ Subgroup.centralizer (primary : Set group)
    · rw [ite_eq_left hcentralizes, ite_eq_right (fun hmember => hnone ⟨element.val, hmember, hcentralizes⟩)]
    · rw [ite_eq_right hcentralizes]
  apply hvalue
  have himage := congrArg (fun hom => hom (centralConjugacyClassSum
    (localizedComplexIntegerRing ideal) conjugacyClass)) hequal
  change centralCharacterResidueHom localBasis ideal localLabel
    (centralNormalizerCoefficientProjection _ primary intermediate hcontains hnormalizes _) = _ at himage
  rw [hprojection, map_zero] at himage
  exact himage.symm

theorem brauerNormalizer_local_block_exists_iff_subconjugate {group : Type*}
    [Group group] [Fintype group] (basis : FiniteIrreducibleCharacterBasis group)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    (prime : ℕ) [Fact prime.Prime] [CharP (ComplexAlgebraicIntegers ⧸ ideal) prime]
    (primary : Subgroup group) (hprimary : IsPGroup prime primary) (intermediate : Subgroup group)
    (hcontains : Subgroup.centralizer (primary : Set group) ≤ intermediate)
    (hnormalizes : intermediate ≤ Subgroup.normalizer (primary : Set group))
    (localBasis : FiniteIrreducibleCharacterBasis intermediate)
    {label : basis.index} {defect : Subgroup group}
    (hdefect : coefficientBlockDefect basis ideal prime label defect) :
    (∃ localLabel : localBasis.index,
      brauerNormalizerCharacterResidueHom ideal prime primary hprimary intermediate hcontains hnormalizes
        localBasis localLabel = centralCharacterResidueHom basis ideal label) ↔
      subgroupSubconjugate primary defect :=
  ⟨brauerNormalizer_subconjugate_of_local_block_exists basis ideal prime primary hprimary intermediate
      hcontains hnormalizes localBasis hdefect,
    brauerNormalizer_local_block_exists_of_subconjugate basis ideal prime primary hprimary intermediate
      hcontains hnormalizes localBasis hdefect⟩

end CFSG.TwoRankLowerBound.Helpers
