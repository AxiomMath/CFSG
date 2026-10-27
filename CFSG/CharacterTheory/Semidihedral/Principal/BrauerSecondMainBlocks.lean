module

public import CFSG.CharacterTheory.Semidihedral.Principal.TensorGapBound
public import CFSG.CharacterTheory.TwoRankLowerBound.PrincipalSectionIntertwining

public section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers

namespace BrauerSecondMain

variable {G : Type*} [Group G] [Fintype G]

theorem characterSubsetProjection_apply_sum (basis : FiniteIrreducibleCharacterBasis G)
    (support : Finset basis.index) (function : G → ℂ) (element : G) :
    characterSubsetProjection basis support function element =
      ∑ label ∈ support, characterPairing function (basis.representation label).character *
        (basis.representation label).character element := by
  simp only [characterSubsetProjection, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul]

theorem characterSubsetProjection_restrict_inv (basis : FiniteIrreducibleCharacterBasis G)
    (χ : basis.index) (H : Subgroup G) (localBasis : FiniteIrreducibleCharacterBasis H)
    (support : Finset localBasis.index) (x : H) :
    characterSubsetProjection localBasis support
        (fun h : H => (basis.representation χ).character h) x⁻¹ =
      starRingEnd ℂ (characterSubsetProjection localBasis support
        (fun h : H => (basis.representation χ).character h) x) := by
  let restricted : FiniteComplexRepresentation H :=
    { vector := (basis.representation χ).vector
      representation := (basis.representation χ).representation.comp H.subtype }
  have hres : restricted.character = fun h : H => (basis.representation χ).character h := rfl
  rw [characterSubsetProjection_apply_sum, characterSubsetProjection_apply_sum, map_sum]
  refine Finset.sum_congr rfl fun θ _ => ?_
  obtain ⟨m, hm⟩ := characterPairing_basis_natural localBasis restricted θ
  rw [hres] at hm
  rw [hm, map_mul, Complex.conj_natCast, finite_character_conjugate_inverse]

theorem brauer_mismatch_residue_zero (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal] (p : ℕ) [Fact p.Prime]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) p] (u : G) (hgroup : IsPGroup p (Subgroup.zpowers u))
    (localBasis :
      FiniteIrreducibleCharacterBasis (Subgroup.centralizer (Subgroup.zpowers u : Set G)))
    (label : basis.index) (θ : localBasis.index)
    (hθ : brauerNormalizerCharacterResidueHom ideal p (Subgroup.zpowers u) hgroup
      (Subgroup.centralizer (Subgroup.zpowers u : Set G)) le_rfl
      (Subgroup.centralizer_le_normalizer _) localBasis θ ≠
        centralCharacterResidueHom basis ideal label) :
    brauerNormalizerCharacterResidueHom ideal p (Subgroup.zpowers u) hgroup
      (Subgroup.centralizer (Subgroup.zpowers u : Set G)) le_rfl
      (Subgroup.centralizer_le_normalizer _) localBasis θ
      (admissibleCharacterSubsetElement basis _
        (coefficientBlock basis (localizedComplexIntegerRing ideal) label)
        (coefficientBlock_admissible basis _ label)) = 0 := by
  obtain ⟨other, hother⟩ := brauerNormalizer_block_image_exists basis ideal p
    (Subgroup.zpowers u) hgroup (Subgroup.centralizer (Subgroup.zpowers u : Set G)) le_rfl
    (Subgroup.centralizer_le_normalizer _) localBasis θ
  have hnot : other ∉ coefficientBlock basis (localizedComplexIntegerRing ideal) label := by
    intro hin
    have hsame := (sameCoefficientBlock_iff_centralCharacterResidueHom_eq basis ideal other
      label).mp (sameCoefficientBlock_symm basis _ ((coefficientBlock_mem_iff _ _ _ _).mp hin))
    exact hθ (hother.trans hsame)
  rw [hother, centralCharacterResidueHom_subset, ite_eq_right hnot]

theorem brauerNormalizerCharacterResidueHom_eq_of_mem_coefficientBlock
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal] (p : ℕ) [Fact p.Prime]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) p] (u : G) (hgroup : IsPGroup p (Subgroup.zpowers u))
    (localBasis :
      FiniteIrreducibleCharacterBasis (Subgroup.centralizer (Subgroup.zpowers u : Set G)))
    {θ localLabel : localBasis.index}
    (hθ : θ ∈ coefficientBlock localBasis (localizedComplexIntegerRing ideal) localLabel) :
    brauerNormalizerCharacterResidueHom ideal p (Subgroup.zpowers u) hgroup
      (Subgroup.centralizer (Subgroup.zpowers u : Set G)) le_rfl
      (Subgroup.centralizer_le_normalizer _) localBasis θ =
    brauerNormalizerCharacterResidueHom ideal p (Subgroup.zpowers u) hgroup
      (Subgroup.centralizer (Subgroup.zpowers u : Set G)) le_rfl
      (Subgroup.centralizer_le_normalizer _) localBasis localLabel := by
  have hequal := (sameCoefficientBlock_iff_centralCharacterResidueHom_eq localBasis ideal
    θ localLabel).mp
      (sameCoefficientBlock_symm localBasis _ ((coefficientBlock_mem_iff _ _ _ _).mp hθ))
  ext value
  change centralCharacterResidueHom localBasis ideal θ _ =
    centralCharacterResidueHom localBasis ideal localLabel _
  rw [hequal]

theorem mismatch_projection_zero_inv (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal] (p : ℕ) [Fact p.Prime]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) p] (u : G) (e : ℕ) (hu : orderOf u ∣ p ^ e)
    (hgroup : IsPGroup p (Subgroup.zpowers u))
    (localBasis :
      FiniteIrreducibleCharacterBasis (Subgroup.centralizer (Subgroup.zpowers u : Set G)))
    (label χ : basis.index)
    (hχ : χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) label)
    (support : Finset localBasis.index)
    (hsupport : characterSubsetAdmissible localBasis (localizedComplexIntegerRing ideal) support)
    (hmismatch : ∀ θ ∈ support, brauerNormalizerCharacterResidueHom ideal p (Subgroup.zpowers u)
      hgroup (Subgroup.centralizer (Subgroup.zpowers u : Set G)) le_rfl
      (Subgroup.centralizer_le_normalizer _) localBasis θ ≠
        centralCharacterResidueHom basis ideal label)
    (ρ : Subgroup.centralizer (Subgroup.zpowers u : Set G)) (hρ : Nat.Coprime p (orderOf ρ)) :
    characterSubsetProjection localBasis support
      (fun h => (basis.representation χ).character h)
        ((⟨u, element_mem_centralizer_zpowers u⟩ :
          Subgroup.centralizer (Subgroup.zpowers u : Set G)) * ρ)⁻¹ = 0 := by
  have hρ' : Nat.Coprime p (orderOf ρ.val) := by rwa [Subgroup.orderOf_coe]
  exact admissible_mismatch_section_projection_zero basis ideal p u e hu localBasis _
    (coefficientBlock_admissible basis _ label) support hsupport
    (fun θ hθ => brauer_mismatch_residue_zero basis ideal p u hgroup localBasis label θ
      (hmismatch θ hθ)) ρ hρ' χ hχ

end BrauerSecondMain

open BrauerSecondMain

variable {G : Type*} [Group G] [Fintype G]

theorem brauer_second_main_theorem (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal] (p : ℕ) [Fact p.Prime]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) p] (u : G) (e : ℕ) (hu : orderOf u ∣ p ^ e)
    (hgroup : IsPGroup p (Subgroup.zpowers u))
    (localBasis :
      FiniteIrreducibleCharacterBasis (Subgroup.centralizer (Subgroup.zpowers u : Set G)))
    (label χ : basis.index)
    (hχ : χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) label)
    (ρ : Subgroup.centralizer (Subgroup.zpowers u : Set G)) (hρ : Nat.Coprime p (orderOf ρ)) :
    (∀ θ : localBasis.index,
      brauerNormalizerCharacterResidueHom ideal p (Subgroup.zpowers u) hgroup
        (Subgroup.centralizer (Subgroup.zpowers u : Set G)) le_rfl
        (Subgroup.centralizer_le_normalizer _) localBasis θ ≠
          centralCharacterResidueHom basis ideal label →
      characterSubsetProjection localBasis
        (coefficientBlock localBasis (localizedComplexIntegerRing ideal) θ)
        (fun h => (basis.representation χ).character h)
          ((⟨u, element_mem_centralizer_zpowers u⟩ :
            Subgroup.centralizer (Subgroup.zpowers u : Set G)) * ρ) = 0) ∧
    (basis.representation χ).character (u * ρ) =
      ∑ β ∈ (Finset.univ.filter fun θ : localBasis.index =>
          brauerNormalizerCharacterResidueHom ideal p (Subgroup.zpowers u) hgroup
            (Subgroup.centralizer (Subgroup.zpowers u : Set G)) le_rfl
            (Subgroup.centralizer_le_normalizer _) localBasis θ =
              centralCharacterResidueHom basis ideal label).image
          (coefficientBlock localBasis (localizedComplexIntegerRing ideal)),
        characterSubsetProjection localBasis β (fun h => (basis.representation χ).character h)
          ((⟨u, element_mem_centralizer_zpowers u⟩ :
            Subgroup.centralizer (Subgroup.zpowers u : Set G)) * ρ) := by
  set x : Subgroup.centralizer (Subgroup.zpowers u : Set G) :=
    (⟨u, element_mem_centralizer_zpowers u⟩ :
      Subgroup.centralizer (Subgroup.zpowers u : Set G)) * ρ with hx
  set f : Subgroup.centralizer (Subgroup.zpowers u : Set G) → ℂ :=
    fun h => (basis.representation χ).character h with hf
  have hflip : ∀ support : Finset localBasis.index,
      characterSubsetProjection localBasis support f x⁻¹ = 0 →
        characterSubsetProjection localBasis support f x = 0 := by
    intro support hzero
    have h := characterSubsetProjection_restrict_inv basis χ _ localBasis support x⁻¹
    rw [inv_inv] at h
    rw [h, hzero, map_zero]
  have hmain : ∀ θ : localBasis.index,
      brauerNormalizerCharacterResidueHom ideal p (Subgroup.zpowers u) hgroup
        (Subgroup.centralizer (Subgroup.zpowers u : Set G)) le_rfl
        (Subgroup.centralizer_le_normalizer _) localBasis θ ≠
          centralCharacterResidueHom basis ideal label →
      characterSubsetProjection localBasis
        (coefficientBlock localBasis (localizedComplexIntegerRing ideal) θ) f x = 0 := by
    intro θ hθ
    apply hflip
    exact mismatch_projection_zero_inv basis ideal p u e hu hgroup localBasis label χ hχ _
      (coefficientBlock_admissible localBasis _ θ)
      (fun θ' hθ' => by
        rw [brauerNormalizerCharacterResidueHom_eq_of_mem_coefficientBlock ideal p u hgroup
          localBasis hθ']
        exact hθ) ρ hρ
  refine ⟨hmain, ?_⟩
  set F := Finset.univ.filter fun θ : localBasis.index =>
    brauerNormalizerCharacterResidueHom ideal p (Subgroup.zpowers u) hgroup
      (Subgroup.centralizer (Subgroup.zpowers u : Set G)) le_rfl
      (Subgroup.centralizer_le_normalizer _) localBasis θ =
        centralCharacterResidueHom basis ideal label with hF
  have hFblocks : ∀ θ ∈ F,
      coefficientBlock localBasis (localizedComplexIntegerRing ideal) θ ⊆ F := by
    intro θ hθ θ' hθ'
    have hsame := brauerNormalizerCharacterResidueHom_eq_of_mem_coefficientBlock ideal p u hgroup
      localBasis hθ'
    simp only [hF, Finset.mem_filter, Finset.mem_univ, true_and] at hθ ⊢
    exact hsame.trans hθ
  have hFadm : characterSubsetAdmissible localBasis (localizedComplexIntegerRing ideal) F :=
    (characterSubsetAdmissible_iff_union_blocks localBasis _ F).mpr hFblocks
  have hcompl : characterSubsetProjection localBasis Fᶜ f x = 0 := by
    apply hflip
    exact mismatch_projection_zero_inv basis ideal p u e hu hgroup localBasis label χ hχ Fᶜ
      (characterSubsetAdmissible_compl localBasis _ F hFadm)
      (fun θ hθ => by
        simpa [hF] using hθ) ρ hρ
  have hsplit := congrFun (characterSubsetProjection_add_compl localBasis F f
    (fun element conjugator => Representation.char_conj _ element.val conjugator.val)) x
  rw [Pi.add_apply, hcompl, add_zero] at hsplit
  have hunion : (F.image (coefficientBlock localBasis (localizedComplexIntegerRing ideal))).biUnion
      id = F := by
    ext θ
    simp only [Finset.mem_biUnion, Finset.mem_image, id]
    constructor
    · rintro ⟨β, ⟨θ', hθ', rfl⟩, hθβ⟩
      exact hFblocks θ' hθ' hθβ
    · intro hθ
      exact ⟨_, ⟨θ, hθ, rfl⟩, coefficientBlock_self_mem localBasis _ θ⟩
  have hdisj : ((F.image (coefficientBlock localBasis (localizedComplexIntegerRing ideal)) :
      Finset (Finset localBasis.index)) : Set (Finset localBasis.index)).PairwiseDisjoint id := by
    intro β hβ β' hβ' hne
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hβ hβ'
    obtain ⟨θ, -, rfl⟩ := hβ
    obtain ⟨θ', -, rfl⟩ := hβ'
    rcases coefficientBlock_disjoint_or_eq localBasis (localizedComplexIntegerRing ideal) θ θ'
      with h | h
    · exact h
    · exact absurd h hne
  have hsum : characterSubsetProjection localBasis F f x =
      ∑ β ∈ F.image (coefficientBlock localBasis (localizedComplexIntegerRing ideal)),
        characterSubsetProjection localBasis β f x := by
    conv_lhs => rw [← hunion]
    rw [characterSubsetProjection_apply_sum, Finset.sum_biUnion hdisj]
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [characterSubsetProjection_apply_sum]
    rfl
  rw [← hsum, hsplit]
  rfl

end CFSG.Semidihedral.Principal
