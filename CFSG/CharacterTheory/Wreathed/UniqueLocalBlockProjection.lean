module

public import CFSG.LocalAnalysis.LyonsUnitaryFour.Blocks.PrincipalSectionKernel

public section

open scoped BigOperators Classical

namespace CFSG.Wreathed

open CFSG.TwoRankLowerBound.Helpers CFSG.RankTwoShapes CFSG.LyonsUnitaryFour

variable {G : Type*} [Group G] [Fintype G]

theorem local_block_projection_zero_of_not_mem (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal] (p : ℕ) [Fact p.Prime]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) p] (u : G) (e : ℕ) (hu : orderOf u ∣ p ^ e)
    (hgroup : IsPGroup p (Subgroup.zpowers u))
    (localBasis :
      FiniteIrreducibleCharacterBasis (Subgroup.centralizer (Subgroup.zpowers u : Set G)))
    (block : basis.index) (localBlock : localBasis.index)
    (hbrauer : brauerNormalizerCharacterResidueHom ideal p (Subgroup.zpowers u) hgroup
      (Subgroup.centralizer (Subgroup.zpowers u : Set G)) le_rfl
      (Subgroup.centralizer_le_normalizer _) localBasis localBlock =
        centralCharacterResidueHom basis ideal block)
    (regular : Subgroup.centralizer (Subgroup.zpowers u : Set G))
    (hregular : Nat.Coprime p (orderOf regular.val)) (label : basis.index)
    (hlabel : label ∉ coefficientBlock basis (localizedComplexIntegerRing ideal) block) :
    characterSubsetProjection localBasis
      (coefficientBlock localBasis (localizedComplexIntegerRing ideal) localBlock)
      (fun member => (basis.representation label).character member.val)
        ((⟨u, element_mem_centralizer_zpowers u⟩ :
          Subgroup.centralizer (Subgroup.zpowers u : Set G)) * regular)⁻¹ = 0 := by
  let ambientSupport := (coefficientBlock basis (localizedComplexIntegerRing ideal) block)ᶜ
  have hambient := characterSubsetAdmissible_compl basis (localizedComplexIntegerRing ideal) _
    (coefficientBlock_admissible basis (localizedComplexIntegerRing ideal) block)
  apply admissible_mismatch_section_projection_zero basis ideal p u e hu localBasis
    ambientSupport hambient _ (coefficientBlock_admissible localBasis _ localBlock) _ regular
    hregular label (Finset.mem_compl.mpr hlabel)
  intro localLabel hmember
  have hequal := (sameCoefficientBlock_iff_centralCharacterResidueHom_eq localBasis ideal
    localLabel localBlock).mp
      (sameCoefficientBlock_symm localBasis _ ((coefficientBlock_mem_iff _ _ _ _).mp hmember))
  change centralCharacterResidueHom localBasis ideal localLabel
    (centralNormalizerCoefficientProjection _ (Subgroup.zpowers u) _ _ _ _) = 0
  rw [hequal]
  have hvalue := congrArg
    (fun hom => hom (admissibleCharacterSubsetElement basis _ ambientSupport hambient)) hbrauer
  rw [centralCharacterResidueHom_subset, ite_eq_right (Finset.notMem_compl.mpr
    (coefficientBlock_self_mem basis _ block))] at hvalue
  exact hvalue

theorem local_block_compl_projection_zero_of_mem (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal] (p : ℕ) [Fact p.Prime]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) p] (u : G) (e : ℕ) (hu : orderOf u ∣ p ^ e)
    (hgroup : IsPGroup p (Subgroup.zpowers u))
    (localBasis :
      FiniteIrreducibleCharacterBasis (Subgroup.centralizer (Subgroup.zpowers u : Set G)))
    (block : basis.index) (localBlock : localBasis.index)
    (hunique : ∀ θ : localBasis.index,
      brauerNormalizerCharacterResidueHom ideal p (Subgroup.zpowers u) hgroup
        (Subgroup.centralizer (Subgroup.zpowers u : Set G)) le_rfl
        (Subgroup.centralizer_le_normalizer _) localBasis θ =
          centralCharacterResidueHom basis ideal block →
        θ ∈ coefficientBlock localBasis (localizedComplexIntegerRing ideal) localBlock)
    (regular : Subgroup.centralizer (Subgroup.zpowers u : Set G))
    (hregular : Nat.Coprime p (orderOf regular.val)) (label : basis.index)
    (hlabel : label ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) block) :
    characterSubsetProjection localBasis
      (coefficientBlock localBasis (localizedComplexIntegerRing ideal) localBlock)ᶜ
      (fun member => (basis.representation label).character member.val)
        ((⟨u, element_mem_centralizer_zpowers u⟩ :
          Subgroup.centralizer (Subgroup.zpowers u : Set G)) * regular)⁻¹ = 0 := by
  let ambientSupport := coefficientBlock basis (localizedComplexIntegerRing ideal) block
  have hambient := coefficientBlock_admissible basis (localizedComplexIntegerRing ideal) block
  have hlocal := characterSubsetAdmissible_compl localBasis (localizedComplexIntegerRing ideal) _
    (coefficientBlock_admissible localBasis (localizedComplexIntegerRing ideal) localBlock)
  apply admissible_mismatch_section_projection_zero basis ideal p u e hu localBasis
    ambientSupport hambient _ hlocal _ regular hregular label hlabel
  intro localLabel hmember
  obtain ⟨ambientLabel, himage⟩ := brauerNormalizer_block_image_exists basis ideal p
    (Subgroup.zpowers u) hgroup (Subgroup.centralizer (Subgroup.zpowers u : Set G)) le_rfl
    (Subgroup.centralizer_le_normalizer _) localBasis localLabel
  have hnot : ambientLabel ∉ ambientSupport := by
    intro hinside
    have hsame := (sameCoefficientBlock_iff_centralCharacterResidueHom_eq basis ideal
      ambientLabel block).mp
        (sameCoefficientBlock_symm basis _ ((coefficientBlock_mem_iff _ _ _ _).mp hinside))
    exact (Finset.mem_compl.mp hmember) (hunique localLabel (himage.trans hsame))
  have hvalue := congrArg
    (fun hom => hom (admissibleCharacterSubsetElement basis _ ambientSupport hambient)) himage
  rw [centralCharacterResidueHom_subset, ite_eq_right hnot] at hvalue
  exact hvalue

theorem unique_local_block_projection_character (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal] (p : ℕ) [Fact p.Prime]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) p] (u : G) (e : ℕ) (hu : orderOf u ∣ p ^ e)
    (hgroup : IsPGroup p (Subgroup.zpowers u))
    (localBasis :
      FiniteIrreducibleCharacterBasis (Subgroup.centralizer (Subgroup.zpowers u : Set G)))
    (block : basis.index) (localBlock : localBasis.index)
    (hbrauer : brauerNormalizerCharacterResidueHom ideal p (Subgroup.zpowers u) hgroup
      (Subgroup.centralizer (Subgroup.zpowers u : Set G)) le_rfl
      (Subgroup.centralizer_le_normalizer _) localBasis localBlock =
        centralCharacterResidueHom basis ideal block)
    (hunique : ∀ θ : localBasis.index,
      brauerNormalizerCharacterResidueHom ideal p (Subgroup.zpowers u) hgroup
        (Subgroup.centralizer (Subgroup.zpowers u : Set G)) le_rfl
        (Subgroup.centralizer_le_normalizer _) localBasis θ =
          centralCharacterResidueHom basis ideal block →
        θ ∈ coefficientBlock localBasis (localizedComplexIntegerRing ideal) localBlock)
    (regular : Subgroup.centralizer (Subgroup.zpowers u : Set G))
    (hregular : Nat.Coprime p (orderOf regular.val)) (label : basis.index) :
    characterSubsetProjection localBasis
      (coefficientBlock localBasis (localizedComplexIntegerRing ideal) localBlock)
      (fun member => (basis.representation label).character member.val)
        ((⟨u, element_mem_centralizer_zpowers u⟩ :
          Subgroup.centralizer (Subgroup.zpowers u : Set G)) * regular)⁻¹ =
    characterSubsetProjection basis
      (coefficientBlock basis (localizedComplexIntegerRing ideal) block)
      (basis.representation label).character
        (((⟨u, element_mem_centralizer_zpowers u⟩ :
          Subgroup.centralizer (Subgroup.zpowers u : Set G)) * regular)⁻¹).val := by
  by_cases hlabel : label ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) block
  · rw [characterSubsetProjection_character basis _ label hlabel]
    have hzero := local_block_compl_projection_zero_of_mem basis ideal p u e hu hgroup localBasis
      block localBlock hunique regular hregular label hlabel
    have hsum := congrFun (characterSubsetProjection_add_compl localBasis
      (coefficientBlock localBasis (localizedComplexIntegerRing ideal) localBlock)
      (fun member => (basis.representation label).character member.val)
      (by intro element conjugator; exact Representation.char_conj _ element.val conjugator.val))
        ((⟨u, element_mem_centralizer_zpowers u⟩ :
          Subgroup.centralizer (Subgroup.zpowers u : Set G)) * regular)⁻¹
    simpa only [Pi.add_apply, hzero, add_zero] using hsum
  · rw [characterSubsetProjection_character_not_mem basis _ label hlabel]
    exact local_block_projection_zero_of_not_mem basis ideal p u e hu hgroup localBasis block
      localBlock hbrauer regular hregular label hlabel

theorem unique_local_block_projection (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal] (p : ℕ) [Fact p.Prime]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) p] (u : G) (e : ℕ) (hu : orderOf u ∣ p ^ e)
    (hgroup : IsPGroup p (Subgroup.zpowers u))
    (localBasis :
      FiniteIrreducibleCharacterBasis (Subgroup.centralizer (Subgroup.zpowers u : Set G)))
    (block : basis.index) (localBlock : localBasis.index)
    (hbrauer : brauerNormalizerCharacterResidueHom ideal p (Subgroup.zpowers u) hgroup
      (Subgroup.centralizer (Subgroup.zpowers u : Set G)) le_rfl
      (Subgroup.centralizer_le_normalizer _) localBasis localBlock =
        centralCharacterResidueHom basis ideal block)
    (hunique : ∀ θ : localBasis.index,
      brauerNormalizerCharacterResidueHom ideal p (Subgroup.zpowers u) hgroup
        (Subgroup.centralizer (Subgroup.zpowers u : Set G)) le_rfl
        (Subgroup.centralizer_le_normalizer _) localBasis θ =
          centralCharacterResidueHom basis ideal block →
        θ ∈ coefficientBlock localBasis (localizedComplexIntegerRing ideal) localBlock)
    (regular : Subgroup.centralizer (Subgroup.zpowers u : Set G))
    (hregular : Nat.Coprime p (orderOf regular.val)) (function : G → ℂ)
    (hclass : ∀ element conjugator : G,
      function (conjugator * element * conjugator⁻¹) = function element) :
    characterSubsetProjection localBasis
      (coefficientBlock localBasis (localizedComplexIntegerRing ideal) localBlock)
      (fun member => function member.val)
        ((⟨u, element_mem_centralizer_zpowers u⟩ :
          Subgroup.centralizer (Subgroup.zpowers u : Set G)) * regular)⁻¹ =
    characterSubsetProjection basis
      (coefficientBlock basis (localizedComplexIntegerRing ideal) block) function
        (((⟨u, element_mem_centralizer_zpowers u⟩ :
          Subgroup.centralizer (Subgroup.zpowers u : Set G)) * regular)⁻¹).val := by
  let restriction : (G → ℂ) →ₗ[ℂ] (Subgroup.centralizer (Subgroup.zpowers u : Set G) → ℂ) :=
    LinearMap.pi fun member => LinearMap.proj member.val
  let sectionPoint := ((⟨u, element_mem_centralizer_zpowers u⟩ :
    Subgroup.centralizer (Subgroup.zpowers u : Set G)) * regular)⁻¹
  let localEvaluation : (G → ℂ) →ₗ[ℂ] ℂ :=
    (LinearMap.proj sectionPoint).comp
      ((characterSubsetProjection localBasis
        (coefficientBlock localBasis (localizedComplexIntegerRing ideal) localBlock)).comp
          restriction)
  let ambientEvaluation : (G → ℂ) →ₗ[ℂ] ℂ :=
    (LinearMap.proj sectionPoint.val).comp
      (characterSubsetProjection basis (coefficientBlock basis (localizedComplexIntegerRing ideal)
        block))
  change localEvaluation function = ambientEvaluation function
  have hexpansion : function = ∑ label,
      characterPairing function (basis.representation label).character •
        (basis.representation label).character := by
    funext element
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using
      finiteIrreducibleCharacterBasis_reconstruction basis function hclass element
  rw [hexpansion, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro label _
  rw [map_smul, map_smul]
  congr 1
  exact unique_local_block_projection_character basis ideal p u e hu hgroup localBasis block
    localBlock hbrauer hunique regular hregular label

theorem unique_local_block_section_kernel_inverse (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal] (p : ℕ) [Fact p.Prime]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) p] (u : G) (e : ℕ) (hu : orderOf u ∣ p ^ e)
    (hgroup : IsPGroup p (Subgroup.zpowers u))
    (localBasis :
      FiniteIrreducibleCharacterBasis (Subgroup.centralizer (Subgroup.zpowers u : Set G)))
    (block : basis.index) (localBlock : localBasis.index)
    (hbrauer : brauerNormalizerCharacterResidueHom ideal p (Subgroup.zpowers u) hgroup
      (Subgroup.centralizer (Subgroup.zpowers u : Set G)) le_rfl
      (Subgroup.centralizer_le_normalizer _) localBasis localBlock =
        centralCharacterResidueHom basis ideal block)
    (hunique : ∀ θ : localBasis.index,
      brauerNormalizerCharacterResidueHom ideal p (Subgroup.zpowers u) hgroup
        (Subgroup.centralizer (Subgroup.zpowers u : Set G)) le_rfl
        (Subgroup.centralizer_le_normalizer _) localBasis θ =
          centralCharacterResidueHom basis ideal block →
        θ ∈ coefficientBlock localBasis (localizedComplexIntegerRing ideal) localBlock)
    (rx ry : Subgroup.centralizer (Subgroup.zpowers u : Set G))
    (hrx : Nat.Coprime p (orderOf rx)) (hry : Nat.Coprime p (orderOf ry)) :
    ∑ label ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) block,
        (basis.representation label).character ((centralizerSelf u * ry : _) : G) *
          (basis.representation label).character ((centralizerSelf u * rx : _) : G)⁻¹ =
      ∑ label ∈ coefficientBlock localBasis (localizedComplexIntegerRing ideal) localBlock,
        (localBasis.representation label).character (centralizerSelf u * ry) *
          (localBasis.representation label).character (centralizerSelf u * rx)⁻¹ := by
  have hreg : Nat.Coprime p (orderOf (rx : G)) := by rwa [Subgroup.orderOf_coe]
  have hlocal := unique_local_block_projection basis ideal p u e hu hgroup localBasis block
    localBlock hbrauer hunique rx hreg (conjugatorCount ((centralizerSelf u * ry : _) : G)⁻¹)
    (conjugatorCount_conjugation ((centralizerSelf u * ry : _) : G)⁻¹)
  have hpt : ((⟨u, element_mem_centralizer_zpowers u⟩ :
      Subgroup.centralizer (Subgroup.zpowers u : Set G)) * rx)⁻¹ =
      (centralizerSelf u * rx)⁻¹ := rfl
  rw [hpt] at hlocal
  have hambient : characterSubsetProjection basis
      (coefficientBlock basis (localizedComplexIntegerRing ideal) block)
      (conjugatorCount ((centralizerSelf u * ry : _) : G)⁻¹)
      (((centralizerSelf u * rx)⁻¹ : Subgroup.centralizer (Subgroup.zpowers u : Set G)) : G) =
      ∑ label ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) block,
        (basis.representation label).character ((centralizerSelf u * ry : _) : G) *
          (basis.representation label).character ((centralizerSelf u * rx : _) : G)⁻¹ := by
    rw [characterSubsetProjection_apply']
    apply Finset.sum_congr rfl
    intro label _
    rw [conjugatorCount_pairing, inv_inv, Subgroup.coe_inv]
  have hmask := congrFun (coefficientBlock_section_mask_commute localBasis ideal p
    localBlock (inverseSection p u) (inverseSection_primeSectionUnion p u e hu)
    (fun h : Subgroup.centralizer (Subgroup.zpowers u : Set G) =>
      conjugatorCount ((centralizerSelf u * ry : _) : G)⁻¹ h.val)) (centralizerSelf u * rx)⁻¹
  have hmem := inv_mem_inverseSection p u rx hrx
  have hunmask : characterFunctionMask (inverseSection p u)
      (characterSubsetProjection localBasis
        (coefficientBlock localBasis (localizedComplexIntegerRing ideal) localBlock)
        fun h : Subgroup.centralizer (Subgroup.zpowers u : Set G) =>
          conjugatorCount ((centralizerSelf u * ry : _) : G)⁻¹ h.val)
        (centralizerSelf u * rx)⁻¹ =
      characterSubsetProjection localBasis
        (coefficientBlock localBasis (localizedComplexIntegerRing ideal) localBlock)
        (fun h : Subgroup.centralizer (Subgroup.zpowers u : Set G) =>
          conjugatorCount ((centralizerSelf u * ry : _) : G)⁻¹ h.val)
        (centralizerSelf u * rx)⁻¹ := by
    unfold characterFunctionMask
    rw [ite_eq_left hmem]
  rw [hunmask, mask_conjugatorCount_eq_local p u e hu (centralizerSelf u * ry) ry rfl hry]
    at hmask
  have hlocalValue : characterSubsetProjection localBasis
      (coefficientBlock localBasis (localizedComplexIntegerRing ideal) localBlock)
      (conjugatorCount (centralizerSelf u * ry)⁻¹) (centralizerSelf u * rx)⁻¹ =
      ∑ label ∈ coefficientBlock localBasis (localizedComplexIntegerRing ideal) localBlock,
        (localBasis.representation label).character (centralizerSelf u * ry) *
          (localBasis.representation label).character (centralizerSelf u * rx)⁻¹ := by
    rw [characterSubsetProjection_apply']
    apply Finset.sum_congr rfl
    intro label _
    rw [conjugatorCount_pairing, inv_inv]
  rw [hlocalValue] at hmask
  rw [← hambient, ← hlocal, hmask]

theorem unique_local_block_section_kernel (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal] (p : ℕ) [Fact p.Prime]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) p] (u : G) (e : ℕ) (hu : orderOf u ∣ p ^ e)
    (hgroup : IsPGroup p (Subgroup.zpowers u))
    (localBasis :
      FiniteIrreducibleCharacterBasis (Subgroup.centralizer (Subgroup.zpowers u : Set G)))
    (block : basis.index) (localBlock : localBasis.index)
    (hbrauer : brauerNormalizerCharacterResidueHom ideal p (Subgroup.zpowers u) hgroup
      (Subgroup.centralizer (Subgroup.zpowers u : Set G)) le_rfl
      (Subgroup.centralizer_le_normalizer _) localBasis localBlock =
        centralCharacterResidueHom basis ideal block)
    (hunique : ∀ θ : localBasis.index,
      brauerNormalizerCharacterResidueHom ideal p (Subgroup.zpowers u) hgroup
        (Subgroup.centralizer (Subgroup.zpowers u : Set G)) le_rfl
        (Subgroup.centralizer_le_normalizer _) localBasis θ =
          centralCharacterResidueHom basis ideal block →
        θ ∈ coefficientBlock localBasis (localizedComplexIntegerRing ideal) localBlock)
    (x y : Subgroup.centralizer (Subgroup.zpowers u : Set G))
    (hx : ∃ r : Subgroup.centralizer (Subgroup.zpowers u : Set G),
      x = centralizerSelf u * r ∧ Nat.Coprime p (orderOf r))
    (hy : ∃ r : Subgroup.centralizer (Subgroup.zpowers u : Set G),
      y = centralizerSelf u * r ∧ Nat.Coprime p (orderOf r)) :
    ∑ label ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) block,
        (basis.representation label).character (x : G) *
          starRingEnd ℂ ((basis.representation label).character (y : G)) =
      ∑ label ∈ coefficientBlock localBasis (localizedComplexIntegerRing ideal) localBlock,
        (localBasis.representation label).character x *
          starRingEnd ℂ ((localBasis.representation label).character y) := by
  obtain ⟨rx, rfl, hrx⟩ := hx
  obtain ⟨ry, rfl, hry⟩ := hy
  simp_rw [finite_character_conjugate_inverse]
  rw [← Subgroup.coe_inv]
  exact unique_local_block_section_kernel_inverse basis ideal p u e hu hgroup localBasis block
    localBlock hbrauer hunique ry rx hry hrx

end CFSG.Wreathed
