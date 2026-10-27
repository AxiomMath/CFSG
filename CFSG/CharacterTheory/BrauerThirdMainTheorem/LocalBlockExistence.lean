module

public import CFSG.CharacterTheory.BrauerThirdMainTheorem.ReducedProjection
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.NormalBlockDefects

public section

open CFSG
namespace CFSG.BrauerThirdMainTheorem.Helpers

theorem residue_factor_through_reduction {ring first second reduced field : Type*}
    [CommRing ring] [CommRing first] [CommRing second] [CommRing reduced] [Field field]
    [Algebra ring first] [Algebra ring second] [Algebra ring reduced] [Algebra ring field]
    (projection : first →ₐ[ring] reduced) (reduction : second →ₐ[ring] reduced)
    (residue : first →ₐ[ring] field)
    (hkernel : RingHom.ker projection.toRingHom ≤ RingHom.ker residue.toRingHom) :
    ∃ subalgebra : Subalgebra ring second,
      ∃ liftedResidue : subalgebra →ₐ[ring] field,
        ∀ (value : first) (lift : second), reduction lift = projection value →
          ∃ hmember : lift ∈ subalgebra,
            liftedResidue ⟨lift, hmember⟩ = residue value := by
  let image := projection.range
  let imageResidue : image →ₐ[ring] field :=
    projection.rangeRestrict.liftOfSurjective projection.rangeRestrict_surjective residue
      (by
        intro value hvalue
        apply hkernel
        rw [RingHom.mem_ker] at hvalue ⊢
        exact congrArg Subtype.val hvalue)
  let subalgebra := image.comap reduction
  let restricted : subalgebra →ₐ[ring] image :=
    (reduction.comp subalgebra.val).codRestrict image (fun value => value.property)
  refine ⟨subalgebra, imageResidue.comp restricted, ?_⟩
  intro value lift hequal
  have hmember : lift ∈ subalgebra := by
    change reduction lift ∈ image
    rw [hequal]
    exact projection.mem_range_self value
  refine ⟨hmember, ?_⟩
  have hreduced : restricted ⟨lift, hmember⟩ = projection.rangeRestrict value :=
    Subtype.ext hequal
  change imageResidue (restricted ⟨lift, hmember⟩) = residue value
  rw [hreduced]
  exact AlgHom.liftOfSurjective_apply _ _ _ _ value

theorem blockDefect_centralChar_mem_of_centralizer_coeff_mem
    (prime : ℕ) (hprime : prime.Prime) (m : Ideal BlocksAlgInt) (hm : m.IsMaximal)
    (G : Type*) [Group G] [Finite G] (subgroup : Subgroup G)
    (hpGroup : IsPGroup prime subgroup) {character coefficients : G → ℂ}
    (hcharacter : character ∈ BlocksIrr G) {defect : Subgroup G}
    (hdefect : blockDefect prime m character defect)
    (hsubconjugate : subgroupSubconjugate subgroup defect)
    (hcoefficients : BlocksIsCentralR m coefficients)
    (hcentralizer : ∀ element ∈ Subgroup.centralizer (subgroup : Set G),
      coefficients element ∈ BlocksLocalMaxIdeal m) :
    BlocksCentralChar character coefficients ∈ BlocksLocalMaxIdeal m := by
  classical
  let : Fintype (ConjClasses G) := Fintype.ofFinite _
  choose representatives hrepresentatives using (fun conjugacyClass : ConjClasses G =>
    ConjClasses.exists_rep conjugacyClass)
  rw [central_class_expansion coefficients hcoefficients.2 representatives hrepresentatives,
    finsum_eq_sum_of_fintype, centralChar_sum]
  apply localMaxIdeal_sum m hm
  intro conjugacyClass _
  rw [centralChar_smul]
  by_cases hscalar : BlocksCentralChar character (classCoefficients conjugacyClass) ∈
      BlocksLocalMaxIdeal m
  · rw [mul_comm]
    exact localMaxIdeal_mul_localRing m hm hscalar (hcoefficients.1 _)
  · obtain ⟨classSubgroup, hclassSubgroup⟩ := classDefect_exists prime conjugacyClass
    have hclassSubconjugate := subgroupSubconjugate_trans hsubconjugate
      (hdefect.2 conjugacyClass hscalar classSubgroup hclassSubgroup)
    obtain ⟨element, helement, helementCentralizes⟩ :=
      (class_meets_centralizer_iff prime hprime hpGroup hclassSubgroup).mpr hclassSubconjugate
    obtain ⟨conjugator, hconjugator⟩ := isConj_iff.mp
      (ConjClasses.mk_eq_mk_iff_isConj.mp ((hrepresentatives conjugacyClass).trans helement.symm))
    have hequal : coefficients element = coefficients (representatives conjugacyClass) := by
      rw [← hconjugator, hcoefficients.2]
    exact localMaxIdeal_mul_localRing m hm (hequal ▸ hcentralizer element helementCentralizes)
      (centralChar_localRing m hm hcharacter (classCoefficients_central m hm conjugacyClass))

theorem reducedBrauerProjection_kernel_le_residue
    (m : Ideal BlocksAlgInt) (hm : m.IsMaximal) (prime : ℕ) (hprime : prime.Prime)
    (hprimeMem : (prime : BlocksAlgInt) ∈ m) (G : Type) [Group G] [Finite G]
    (subgroup overgroup : Subgroup G) (hpGroup : IsPGroup prime subgroup)
    (hcentralizer : Subgroup.centralizer (subgroup : Set G) ≤ overgroup)
    (hnormalizer : overgroup ≤ Subgroup.normalizer (subgroup : Set G))
    (character : BlocksIrr G) {defect : Subgroup G}
    (hdefect : blockDefect prime m character.val defect)
    (hsubconjugate : subgroupSubconjugate subgroup defect) :
    RingHom.ker (reducedBrauerProjection m hm prime hprime hprimeMem G subgroup overgroup
      hpGroup hcentralizer hnormalizer).toRingHom ≤
      RingHom.ker (centralResidueAlgHom m hm G character).toRingHom := by
  intro value hvalue
  rw [RingHom.mem_ker] at hvalue ⊢
  apply (localResidue_eq_zero_iff m hm _).mpr
  apply blockDefect_centralChar_mem_of_centralizer_coeff_mem prime hprime m hm G subgroup
    hpGroup character.property hdefect hsubconjugate
    (centralLocalCoefficients_central m hm G value)
  intro element helement
  let localElement : overgroup := ⟨element, hcentralizer helement⟩
  have hcoeff := congrArg (fun reducedValue : Subalgebra.center (localCoefficientSubring m hm)
      (MonoidAlgebra (localResidueField m hm) overgroup) => reducedValue.val.coeff localElement) hvalue
  change localResidue m hm
      ((localBrauerElement m hm G subgroup overgroup hnormalizer value).val.coeff localElement) =
    0 at hcoeff
  have hmember := (localResidue_eq_zero_iff m hm _).mp hcoeff
  change centralLocalCoefficients m hm overgroup
    (localBrauerElement m hm G subgroup overgroup hnormalizer value) localElement ∈
      BlocksLocalMaxIdeal m at hmember
  rw [localBrauerElement_coefficients, brauerProj_apply, ite_eq_left helement] at hmember
  exact hmember

theorem brauerCorr_of_scalar_congr (m : Ideal BlocksAlgInt) (hm : m.IsMaximal)
    (G : Type) [Group G] [Finite G] (subgroup overgroup : Subgroup G)
    (hnormalizer : overgroup ≤ Subgroup.normalizer (subgroup : Set G))
    {block : Set (G → ℂ)} {localBlock : Set (overgroup → ℂ)}
    (hblock : BlocksIsBlock m G block) (hlocalBlock : BlocksIsBlock m overgroup localBlock)
    {character : G → ℂ} {localCharacter : overgroup → ℂ}
    (hcharacter : character ∈ block) (hlocalCharacter : localCharacter ∈ localBlock)
    (hcongr : ∀ coefficients : G → ℂ, BlocksIsCentralR m coefficients →
      BlocksCentralChar character coefficients -
        BlocksCentralChar localCharacter (BlocksBrauerProj subgroup overgroup coefficients) ∈
          BlocksLocalMaxIdeal m) :
    BlocksBrauerCorr m subgroup overgroup localBlock block := by
  intro coefficients hcoefficients left hleft right hright
  have hleftScalar := block_centralChar_congr m hm G hblock hcharacter hleft hcoefficients
  have hrightScalar := block_centralChar_congr m hm overgroup hlocalBlock hlocalCharacter hright
    (brauerProj_central m hm subgroup overgroup hnormalizer hcoefficients)
  have hnegative := localMaxIdeal_neg m hrightScalar
  have hnegative' : BlocksCentralChar localCharacter (BlocksBrauerProj subgroup overgroup coefficients) -
      BlocksCentralChar right (BlocksBrauerProj subgroup overgroup coefficients) ∈ BlocksLocalMaxIdeal m := by
    simpa only [neg_sub] using hnegative
  exact localMaxIdeal_trans m hm
    (localMaxIdeal_trans m hm hleftScalar (hcongr coefficients hcoefficients)) hnegative'

set_option maxHeartbeats 2000000 in
theorem localBlock_exists_of_subconjugate_defect
    (m : Ideal BlocksAlgInt) (hm : m.IsMaximal) (prime : ℕ) (hprime : prime.Prime)
    (hprimeMem : (prime : BlocksAlgInt) ∈ m) (G : Type) [Group G] [Finite G]
    (subgroup overgroup : Subgroup G) (hpGroup : IsPGroup prime subgroup)
    (hcentralizer : Subgroup.centralizer (subgroup : Set G) ≤ overgroup)
    (hnormalizer : overgroup ≤ Subgroup.normalizer (subgroup : Set G))
    {block : Set (G → ℂ)} (hblock : BlocksIsBlock m G block)
    {character : G → ℂ} (hcharacter : character ∈ block) {defect : Subgroup G}
    (hdefect : blockDefect prime m character defect)
    (hsubconjugate : subgroupSubconjugate subgroup defect) :
    ∃ localBlock : Set (overgroup → ℂ), BlocksIsBlock m overgroup localBlock ∧
      BlocksBrauerCorr m subgroup overgroup localBlock block := by
  classical
  let irreducible : BlocksIrr G := ⟨character, block_subset_irr m hblock hcharacter⟩
  let projection := reducedBrauerProjection m hm prime hprime hprimeMem G subgroup overgroup
    hpGroup hcentralizer hnormalizer
  have hkernel : RingHom.ker projection.toRingHom ≤
      RingHom.ker (centralResidueAlgHom m hm G irreducible).toRingHom :=
    reducedBrauerProjection_kernel_le_residue m hm prime hprime hprimeMem G subgroup overgroup
      hpGroup hcentralizer hnormalizer irreducible hdefect hsubconjugate
  have hfactorization := @residue_factor_through_reduction
    (localCoefficientSubring m hm)
    (Subalgebra.center (localCoefficientSubring m hm)
      (MonoidAlgebra (localCoefficientSubring m hm) G))
    (Subalgebra.center (localCoefficientSubring m hm)
      (MonoidAlgebra (localCoefficientSubring m hm) overgroup))
    (Subalgebra.center (localCoefficientSubring m hm)
      (MonoidAlgebra (localResidueField m hm) overgroup))
    (localResidueField m hm)
    inferInstance inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance
    projection (centerReduction m hm overgroup) (centralResidueAlgHom m hm G irreducible) hkernel
  obtain ⟨subalgebra, liftedResidue, hlifted⟩ := hfactorization
  obtain ⟨localCharacter, hlocalCharacter⟩ :=
    centralSubalgebra_residue_extension m hm overgroup subalgebra liftedResidue
  refine ⟨BlocksBlockOf m overgroup localCharacter.val,
    ⟨localCharacter.val, localCharacter.property, rfl⟩, ?_⟩
  apply brauerCorr_of_scalar_congr m hm G subgroup overgroup hnormalizer hblock
    ⟨localCharacter.val, localCharacter.property, rfl⟩ hcharacter
    (mem_blockOf_self m localCharacter.property)
  intro coefficients hcoefficients
  let : Fintype G := Fintype.ofFinite _
  let value := centralLocalElement m hm G coefficients hcoefficients
  let lift := localBrauerElement m hm G subgroup overgroup hnormalizer value
  obtain ⟨hmember, hequal⟩ := hlifted value lift rfl
  rw [hlocalCharacter ⟨lift, hmember⟩] at hequal
  have hcongr := (localResidue_eq_iff m hm _ _).mp hequal.symm
  change BlocksCentralChar character (centralLocalCoefficients m hm G value) -
    BlocksCentralChar localCharacter.val (centralLocalCoefficients m hm overgroup lift) ∈
      BlocksLocalMaxIdeal m at hcongr
  rw [localBrauerElement_coefficients, centralLocalElement_coefficients] at hcongr
  exact hcongr

end CFSG.BrauerThirdMainTheorem.Helpers
