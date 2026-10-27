module

public import CFSG.CharacterTheory.TwoRankLowerBound.RelativeCentralizerResidues
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection1.PFsection1_5

public section

open scoped BigOperators Classical

namespace CFSG.Wreathed

open CFSG.TwoRankLowerBound.Helpers

namespace BlockOrbits

section Transport

variable {C C' : Type*} [Group C] [Fintype C] [Group C'] [Fintype C']

@[expose] def LabelTransport (sourceBasis : FiniteIrreducibleCharacterBasis C)
    (targetBasis : FiniteIrreducibleCharacterBasis C') (e : C ≃* C') (θ : sourceBasis.index)
    (θ' : targetBasis.index) : Prop :=
  ∀ x : C, (targetBasis.representation θ').character (e x) =
    (sourceBasis.representation θ).character x

theorem labelTransport_exists (sourceBasis : FiniteIrreducibleCharacterBasis C)
    (targetBasis : FiniteIrreducibleCharacterBasis C') (e : C ≃* C') (θ : sourceBasis.index) :
    ∃ θ', LabelTransport sourceBasis targetBasis e θ θ' := by
  let data : FiniteComplexRepresentation C' :=
    { vector := (sourceBasis.representation θ).vector
      representation := (sourceBasis.representation θ).representation.comp e.symm.toMonoidHom }
  have hirreducible : data.IsIrreducible := by
    let : (sourceBasis.representation θ).representation.IsIrreducible := sourceBasis.irreducible θ
    exact CFSG.Section1.irreducible_compMulEquivDomain _ e.symm
  obtain ⟨θ', hθ'⟩ := finiteIrreducibleCharacterBasis_contains_irreducible targetBasis data
    hirreducible
  refine ⟨θ', fun x => ?_⟩
  rw [hθ']
  change LinearMap.trace ℂ _ ((sourceBasis.representation θ).representation (e.symm (e x))) = _
  rw [e.symm_apply_apply]
  rfl

theorem labelTransport_unique {sourceBasis : FiniteIrreducibleCharacterBasis C}
    {targetBasis : FiniteIrreducibleCharacterBasis C'} {e : C ≃* C'} {θ : sourceBasis.index}
    {θ₁ θ₂ : targetBasis.index} (h₁ : LabelTransport sourceBasis targetBasis e θ θ₁)
    (h₂ : LabelTransport sourceBasis targetBasis e θ θ₂) : θ₁ = θ₂ := by
  apply targetBasis.distinct
  funext y
  obtain ⟨x, rfl⟩ := e.surjective y
  exact (h₁ x).trans (h₂ x).symm

theorem centralCharacterScalar_labelTransport (sourceBasis : FiniteIrreducibleCharacterBasis C)
    (targetBasis : FiniteIrreducibleCharacterBasis C') (e : C ≃* C') {θ : sourceBasis.index}
    {θ' : targetBasis.index} (h : LabelTransport sourceBasis targetBasis e θ θ')
    (z : MonoidAlgebra ℂ C) :
    centralCharacterScalar targetBasis (MonoidAlgebra.mapDomainRingHom ℂ e.toMonoidHom z) θ' =
      centralCharacterScalar sourceBasis z θ := by
  have hcard : Nat.card C' = Nat.card C := (Nat.card_congr e.toEquiv).symm
  have hdegree : (targetBasis.representation θ').character 1 =
      (sourceBasis.representation θ).character 1 := by
    have := h 1
    rwa [map_one] at this
  unfold centralCharacterScalar characterPairing
  rw [hcard, hdegree]
  congr 3
  refine (Fintype.sum_bijective e e.bijective _ _ fun x => ?_).symm
  dsimp only
  rw [groupAlgebra_transport_coeff, ← map_inv, e.symm_apply_apply, h]

theorem centralCharacterResidueHom_labelTransport (sourceBasis : FiniteIrreducibleCharacterBasis C)
    (targetBasis : FiniteIrreducibleCharacterBasis C') (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] (e : C ≃* C') {θ : sourceBasis.index} {θ' : targetBasis.index}
    (h : LabelTransport sourceBasis targetBasis e θ θ')
    (z : centralCoefficientSubring (G := C) (localizedComplexIntegerRing ideal)) :
    centralCharacterResidueHom targetBasis ideal θ' (centralCoefficientTransport _ e z) =
      centralCharacterResidueHom sourceBasis ideal θ z := by
  change localizedComplexIntegerResidue ideal (localCentralCharacterHom targetBasis ideal θ' _) =
    localizedComplexIntegerResidue ideal (localCentralCharacterHom sourceBasis ideal θ z)
  congr 1
  apply Subtype.ext
  rw [localCentralCharacterHom_coe, localCentralCharacterHom_coe]
  exact centralCharacterScalar_labelTransport sourceBasis targetBasis e h z.val

theorem sameCoefficientBlock_labelTransport_iff (sourceBasis : FiniteIrreducibleCharacterBasis C)
    (targetBasis : FiniteIrreducibleCharacterBasis C') (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] (e : C ≃* C') {θ₁ θ₂ : sourceBasis.index} {θ₁' θ₂' : targetBasis.index}
    (h₁ : LabelTransport sourceBasis targetBasis e θ₁ θ₁')
    (h₂ : LabelTransport sourceBasis targetBasis e θ₂ θ₂') :
    sameCoefficientBlock sourceBasis (localizedComplexIntegerRing ideal) θ₁ θ₂ ↔
      sameCoefficientBlock targetBasis (localizedComplexIntegerRing ideal) θ₁' θ₂' := by
  rw [sameCoefficientBlock_iff_centralCharacterResidueHom_eq,
    sameCoefficientBlock_iff_centralCharacterResidueHom_eq]
  constructor
  · intro hequal
    apply RingHom.ext
    intro w
    have hw := centralCoefficientTransport_inverse (localizedComplexIntegerRing ideal) e.symm w
    rw [MulEquiv.symm_symm] at hw
    rw [← hw, centralCharacterResidueHom_labelTransport sourceBasis targetBasis ideal e h₁,
      centralCharacterResidueHom_labelTransport sourceBasis targetBasis ideal e h₂, hequal]
  · intro hequal
    apply RingHom.ext
    intro z
    rw [← centralCharacterResidueHom_labelTransport sourceBasis targetBasis ideal e h₁,
      ← centralCharacterResidueHom_labelTransport sourceBasis targetBasis ideal e h₂, hequal]

end Transport

section Embedded

variable {K C : Type*} [Group K] [Group C]

theorem embedded_coeff (ι : C →* K) (hι : Function.Injective ι) (value : MonoidAlgebra ℂ C)
    (x : C) : (MonoidAlgebra.mapDomainRingHom ℂ ι value).coeff (ι x) = value.coeff x := by
  rw [MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.coeff_mapDomain]
  exact Finsupp.mapDomain_apply_of_injective hι value.coeff x

theorem embedded_coeff_zero (ι : C →* K) (value : MonoidAlgebra ℂ C) (y : K)
    (hy : y ∉ Set.range ι) : (MonoidAlgebra.mapDomainRingHom ℂ ι value).coeff y = 0 := by
  rw [MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.coeff_mapDomain]
  exact Finsupp.mapDomain_of_notMem_range _ _ hy

@[expose] noncomputable def embeddedCommonCentralSubring (ring : Subring ℂ) (ι : C →* K) :
    Subring (centralCoefficientSubring (G := C) ring) :=
  (Subring.center (MonoidAlgebra ℂ K)).comap
    ((MonoidAlgebra.mapDomainRingHom ℂ ι).comp (centralCoefficientSubring (G := C) ring).subtype)

@[expose] noncomputable def embeddedCommonCentralInclusion (ring : Subring ℂ) (ι : C →* K)
    (hι : Function.Injective ι) :
    embeddedCommonCentralSubring ring ι →+* centralCoefficientSubring (G := K) ring where
  toFun value := ⟨MonoidAlgebra.mapDomainRingHom ℂ ι value.val.val, by
    constructor
    · intro element
      by_cases hmember : element ∈ Set.range ι
      · obtain ⟨x, rfl⟩ := hmember
        rw [embedded_coeff ι hι]
        exact centralCoefficientSubring_coefficients ring value.val x
      · rw [embedded_coeff_zero ι _ element hmember]
        exact ring.zero_mem
    · exact value.property⟩
  map_one' := Subtype.ext (map_one _)
  map_zero' := Subtype.ext (map_zero _)
  map_add' left right := Subtype.ext (map_add _ left.val.val right.val.val)
  map_mul' left right := Subtype.ext (map_mul _ left.val.val right.val.val)

theorem embeddedCommonCentralInclusion_val (ring : Subring ℂ) (ι : C →* K)
    (hι : Function.Injective ι) (value : embeddedCommonCentralSubring ring ι) :
    (embeddedCommonCentralInclusion ring ι hι value).val =
      MonoidAlgebra.mapDomainRingHom ℂ ι value.val.val := rfl

theorem embeddedCommonCentral_scalar_mem (ring : Subring ℂ) (ι : C →* K) (scalar : ring) :
    centralCoefficientScalarHom (G := C) ring scalar ∈ embeddedCommonCentralSubring ring ι := by
  change MonoidAlgebra.mapDomainRingHom ℂ ι (MonoidAlgebra.single 1 scalar.val) ∈
    Subring.center (MonoidAlgebra ℂ K)
  rw [MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_single, map_one]
  exact (centralCoefficientScalarHom (G := K) ring scalar).property.2

theorem embeddedCommonCentralInclusion_scalar (ring : Subring ℂ) (ι : C →* K)
    (hι : Function.Injective ι) (scalar : ring) :
    embeddedCommonCentralInclusion ring ι hι
      ⟨centralCoefficientScalarHom ring scalar, embeddedCommonCentral_scalar_mem ring ι scalar⟩ =
        centralCoefficientScalarHom ring scalar := by
  apply Subtype.ext
  change MonoidAlgebra.mapDomainRingHom ℂ ι (MonoidAlgebra.single 1 scalar.val) =
    MonoidAlgebra.single 1 scalar.val
  rw [MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_single, map_one]

variable [Fintype K] [Fintype C]

omit [Fintype K] [Fintype C] in
theorem embeddedCommonCentralInclusion_injective (ring : Subring ℂ) (ι : C →* K)
    (hι : Function.Injective ι) :
    Function.Injective (embeddedCommonCentralInclusion ring ι hι) := by
  intro left right hequal
  apply Subtype.ext
  apply Subtype.ext
  ext x
  have h := congrArg (fun value => value.val.coeff (ι x)) hequal
  simp only [embeddedCommonCentralInclusion_val, embedded_coeff ι hι] at h
  exact h

variable (basis : FiniteIrreducibleCharacterBasis K)
  (localBasis : FiniteIrreducibleCharacterBasis C)
  (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal] (ι : C →* K)
  (hι : Function.Injective ι)

@[expose] def EmbeddedResidueMatch (χ : basis.index) (θ : localBasis.index) : Prop :=
  ∀ a : embeddedCommonCentralSubring (localizedComplexIntegerRing ideal) ι,
    centralCharacterResidueHom localBasis ideal θ a.val =
      centralCharacterResidueHom basis ideal χ (embeddedCommonCentralInclusion _ ι hι a)

theorem embeddedResidueMatch_restriction_exists (χ : basis.index) :
    ∃ θ, EmbeddedResidueMatch basis localBasis ideal ι hι χ θ := by
  obtain ⟨θ, hequal⟩ := centralSubalgebraResidue_extension localBasis ideal
    (embeddedCommonCentralSubring _ ι) (embeddedCommonCentral_scalar_mem _ ι)
    ((centralCharacterResidueHom basis ideal χ).comp (embeddedCommonCentralInclusion _ ι hι)) (by
      intro scalar
      rw [RingHom.comp_apply, embeddedCommonCentralInclusion_scalar,
        centralCharacterResidueHom_scalar])
  exact ⟨θ, fun a => (congrArg (fun hom => hom a) hequal).symm⟩

theorem embeddedResidueMatch_extension_exists (θ : localBasis.index) :
    ∃ χ, EmbeddedResidueMatch basis localBasis ideal ι hι χ θ := by
  let scalar :=
    (centralCoefficientScalarHom (G := C) (localizedComplexIntegerRing ideal)).codRestrict
      (embeddedCommonCentralSubring _ ι) (embeddedCommonCentral_scalar_mem _ ι)
  obtain ⟨χ, hχ⟩ := centralSubalgebraResidue_extension_from_inclusion basis ideal
    (embeddedCommonCentralInclusion _ ι hι) (embeddedCommonCentralInclusion_injective _ ι hι) scalar
    (embeddedCommonCentralInclusion_scalar _ ι hι)
    ((centralCharacterResidueHom localBasis ideal θ).comp
      (embeddedCommonCentralSubring _ ι).subtype)
    (centralCharacterResidueHom_scalar localBasis ideal θ)
  exact ⟨χ, fun a => (hχ a).symm⟩

theorem embeddedResidueMatch_of_same {χ : basis.index} {θ₁ θ₂ : localBasis.index}
    (hsame : sameCoefficientBlock localBasis (localizedComplexIntegerRing ideal) θ₁ θ₂)
    (hmatch : EmbeddedResidueMatch basis localBasis ideal ι hι χ θ₁) :
    EmbeddedResidueMatch basis localBasis ideal ι hι χ θ₂ := by
  intro a
  rw [← (sameCoefficientBlock_iff_centralCharacterResidueHom_eq localBasis ideal θ₁ θ₂).mp hsame]
  exact hmatch a

theorem embeddedResidueMatch_iff_of_same {χ₁ χ₂ : basis.index}
    (hsame : sameCoefficientBlock basis (localizedComplexIntegerRing ideal) χ₁ χ₂)
    (θ : localBasis.index) :
    EmbeddedResidueMatch basis localBasis ideal ι hι χ₁ θ ↔
      EmbeddedResidueMatch basis localBasis ideal ι hι χ₂ θ := by
  unfold EmbeddedResidueMatch
  rw [(sameCoefficientBlock_iff_centralCharacterResidueHom_eq basis ideal χ₁ χ₂).mp hsame]

theorem embeddedResidueMatch_injective
    (hdetermined : ∀ z : centralCoefficientSubring (G := K) (localizedComplexIntegerRing ideal),
      ∃ a : embeddedCommonCentralSubring (localizedComplexIntegerRing ideal) ι, ∀ χ : basis.index,
        centralCharacterResidueHom basis ideal χ z =
          centralCharacterResidueHom basis ideal χ (embeddedCommonCentralInclusion _ ι hι a))
    {χ₁ χ₂ : basis.index} {θ : localBasis.index}
    (h₁ : EmbeddedResidueMatch basis localBasis ideal ι hι χ₁ θ)
    (h₂ : EmbeddedResidueMatch basis localBasis ideal ι hι χ₂ θ) :
    sameCoefficientBlock basis (localizedComplexIntegerRing ideal) χ₁ χ₂ := by
  rw [sameCoefficientBlock_iff_centralCharacterResidueHom_eq]
  apply RingHom.ext
  intro z
  obtain ⟨a, ha⟩ := hdetermined z
  rw [ha χ₁, ha χ₂, ← h₁ a, ← h₂ a]

variable (conj : K → C ≃* C) (hconj : ∀ k x, ι (conj k x) = k * ι x * k⁻¹)

omit [Fintype K] [Fintype C] in
include hι hconj in
theorem embedded_conj_mul_apply (k k' : K) (x : C) : conj (k * k') x = conj k (conj k' x) := by
  apply hι
  rw [hconj, hconj, hconj]
  group

omit [Fintype K] [Fintype C] in
include hι hconj in
theorem embedded_conj_one_apply (x : C) : conj 1 x = x := by
  apply hι
  rw [hconj]
  group

omit [Fintype K] [Fintype C] in
include hι hconj in
theorem embedded_transport_fixes (k : K)
    (a : embeddedCommonCentralSubring (localizedComplexIntegerRing ideal) ι) :
    centralCoefficientTransport _ (conj k) a.val = a.val := by
  apply Subtype.ext
  ext x
  rw [centralCoefficientTransport_coeff]
  have hcentral : ∀ other : MonoidAlgebra ℂ K,
      Commute (MonoidAlgebra.mapDomainRingHom ℂ ι a.val.val) other := by
    intro other
    exact (Subring.mem_center_iff.mp a.property other).symm
  have hcoeff := central_groupAlgebra_coeff_conjugation _ hcentral (ι ((conj k).symm x)) k
  rw [← hconj, MulEquiv.apply_symm_apply, embedded_coeff ι hι, embedded_coeff ι hι] at hcoeff
  exact hcoeff.symm

include hconj in
theorem embeddedResidueMatch_transport {χ : basis.index} {θ θ' : localBasis.index} (k : K)
    (htransport : LabelTransport localBasis localBasis (conj k) θ θ') :
    EmbeddedResidueMatch basis localBasis ideal ι hι χ θ ↔
      EmbeddedResidueMatch basis localBasis ideal ι hι χ θ' := by
  have hequal : ∀ a : embeddedCommonCentralSubring (localizedComplexIntegerRing ideal) ι,
      centralCharacterResidueHom localBasis ideal θ' a.val =
        centralCharacterResidueHom localBasis ideal θ a.val := by
    intro a
    rw [← centralCharacterResidueHom_labelTransport localBasis localBasis ideal (conj k) htransport,
      embedded_transport_fixes ideal ι hι conj hconj k a]
  unfold EmbeddedResidueMatch
  simp only [hequal]

noncomputable def conjugateLabel (k : K) (θ : localBasis.index) : localBasis.index :=
  Classical.choose (labelTransport_exists localBasis localBasis (conj k) θ)

omit [Group K] [Fintype K] in
theorem conjugateLabel_spec (k : K) (θ : localBasis.index) :
    LabelTransport localBasis localBasis (conj k) θ (conjugateLabel localBasis conj k θ) :=
  Classical.choose_spec (labelTransport_exists localBasis localBasis (conj k) θ)

noncomputable def orbitLabels (θ₀ : localBasis.index) : Finset localBasis.index :=
  Finset.univ.filter fun θ => ∃ k : K,
    θ ∈ coefficientBlock localBasis (localizedComplexIntegerRing ideal)
      (conjugateLabel localBasis conj k θ₀)

omit [Group K] in
theorem mem_orbitLabels_iff (θ₀ θ : localBasis.index) :
    θ ∈ orbitLabels localBasis ideal conj θ₀ ↔
      ∃ k θ', LabelTransport localBasis localBasis (conj k) θ₀ θ' ∧
        sameCoefficientBlock localBasis (localizedComplexIntegerRing ideal) θ' θ := by
  simp only [orbitLabels, Finset.mem_filter, Finset.mem_univ, true_and, coefficientBlock_mem_iff]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, _, conjugateLabel_spec localBasis conj k θ₀, hk⟩
  · rintro ⟨k, θ', hθ', hsame⟩
    refine ⟨k, ?_⟩
    rwa [labelTransport_unique (conjugateLabel_spec localBasis conj k θ₀) hθ']

omit [Group K] in
theorem orbitLabels_admissible (θ₀ : localBasis.index) :
    characterSubsetAdmissible localBasis (localizedComplexIntegerRing ideal)
      (orbitLabels localBasis ideal conj θ₀) := by
  let family : Finset (Finset localBasis.index) := Finset.univ.image fun k : K =>
    (coefficientBlock localBasis (localizedComplexIntegerRing ideal)
      (conjugateLabel localBasis conj k θ₀))ᶜ
  have hfamily := characterSubsetAdmissible_finite_intersection localBasis
    (localizedComplexIntegerRing ideal) family (by
      intro support hsupport
      obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hsupport
      exact characterSubsetAdmissible_compl _ _ _ (coefficientBlock_admissible _ _ _))
  have hequal : orbitLabels localBasis ideal conj θ₀ =
      (Finset.univ.filter fun label => ∀ support ∈ family, label ∈ support)ᶜ := by
    ext θ
    simp only [orbitLabels, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl]
    constructor
    · rintro ⟨k, hk⟩ hall
      exact (Finset.mem_compl.mp (hall _ (Finset.mem_image_of_mem _ (Finset.mem_univ k)))) hk
    · intro hnot
      by_contra hnone
      push Not at hnone
      apply hnot
      intro support hsupport
      obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hsupport
      exact Finset.mem_compl.mpr (hnone k)
  rw [hequal]
  exact characterSubsetAdmissible_compl _ _ _ hfamily

include hι hconj in
theorem orbitLabels_transport {θ₀ θ θ' : localBasis.index} (k : K)
    (htransport : LabelTransport localBasis localBasis (conj k) θ θ')
    (hθ : θ ∈ orbitLabels localBasis ideal conj θ₀) :
    θ' ∈ orbitLabels localBasis ideal conj θ₀ := by
  rw [mem_orbitLabels_iff] at hθ ⊢
  obtain ⟨k₀, θ₁, hθ₁, hsame⟩ := hθ
  obtain ⟨θ₂, hθ₂⟩ := labelTransport_exists localBasis localBasis (conj k) θ₁
  refine ⟨k * k₀, θ₂, fun x => ?_, ?_⟩
  · rw [embedded_conj_mul_apply ι hι conj hconj, hθ₂, hθ₁]
  · exact (sameCoefficientBlock_labelTransport_iff localBasis localBasis ideal (conj k) hθ₂
      htransport).mp hsame

omit [Fintype K] in
include hι hconj in
theorem labelTransport_inv {θ θ' : localBasis.index} (k : K)
    (htransport : LabelTransport localBasis localBasis (conj k) θ θ') :
    LabelTransport localBasis localBasis (conj k⁻¹) θ' θ := by
  intro y
  have hy : y = conj k (conj k⁻¹ y) := by
    rw [← embedded_conj_mul_apply ι hι conj hconj, mul_inv_cancel, embedded_conj_one_apply ι hι conj
      hconj]
  conv_rhs => rw [hy]
  exact (htransport _).symm

noncomputable def orbitIdempotent (θ₀ : localBasis.index) :
    centralCoefficientSubring (G := C) (localizedComplexIntegerRing ideal) :=
  admissibleCharacterSubsetElement localBasis _ (orbitLabels localBasis ideal conj θ₀)
    (orbitLabels_admissible localBasis ideal conj θ₀)

include hι hconj in
theorem orbitIdempotent_transport (θ₀ : localBasis.index) (k : K) :
    centralCoefficientTransport _ (conj k) (orbitIdempotent localBasis ideal conj θ₀) =
      orbitIdempotent localBasis ideal conj θ₀ := by
  set e := orbitIdempotent localBasis ideal conj θ₀ with he
  have hscalar : ∀ θ, centralCharacterScalar localBasis e.val θ =
      if θ ∈ orbitLabels localBasis ideal conj θ₀ then 1 else 0 := fun θ =>
    centralComplexCharacterHom_subset localBasis _ _
      (orbitLabels_admissible localBasis ideal conj θ₀) θ
  apply Subtype.ext
  have hleft := centralCharacterScalar_reconstruction localBasis
    (centralCoefficientTransport _ (conj k) e).val
    (centralCoefficientSubring_commutes _ (centralCoefficientTransport _ (conj k) e))
  have hright := centralCharacterScalar_reconstruction localBasis e.val
    (centralCoefficientSubring_commutes _ e)
  rw [hleft, hright]
  congr 1
  funext θ'
  obtain ⟨θ, hθ⟩ := labelTransport_exists localBasis localBasis (conj k⁻¹) θ'
  have htransport : LabelTransport localBasis localBasis (conj k) θ θ' :=
    labelTransport_inv localBasis ι hι conj hconj k⁻¹ hθ |> fun h => by
      rwa [inv_inv] at h
  change centralCharacterScalar localBasis
    (MonoidAlgebra.mapDomainRingHom ℂ (conj k).toMonoidHom e.val) θ' = _
  rw [centralCharacterScalar_labelTransport localBasis localBasis (conj k) htransport, hscalar,
    hscalar]
  have hiff :
      θ ∈ orbitLabels localBasis ideal conj θ₀ ↔ θ' ∈ orbitLabels localBasis ideal conj θ₀ :=
    ⟨orbitLabels_transport localBasis ideal ι hι conj hconj k htransport,
      orbitLabels_transport localBasis ideal ι hι conj hconj k⁻¹ hθ⟩
  simp only [hiff]

include hι hconj in
theorem orbitIdempotent_mem (θ₀ : localBasis.index) :
    orbitIdempotent localBasis ideal conj θ₀ ∈
      embeddedCommonCentralSubring (localizedComplexIntegerRing ideal) ι := by
  set e := orbitIdempotent localBasis ideal conj θ₀ with he
  change MonoidAlgebra.mapDomainRingHom ℂ ι e.val ∈ Subring.center (MonoidAlgebra ℂ K)
  apply Subring.mem_center_iff.mpr
  intro other
  apply Commute.symm
  apply groupAlgebra_central_of_coeff_conjugation
  intro y k
  by_cases hy : y ∈ Set.range ι
  · obtain ⟨x, rfl⟩ := hy
    rw [← hconj, embedded_coeff ι hι, embedded_coeff ι hι]
    have hfix := congrArg (fun value => value.val.coeff (conj k x))
      (orbitIdempotent_transport localBasis ideal ι hι conj hconj θ₀ k)
    simp only [centralCoefficientTransport_coeff, MulEquiv.symm_apply_apply] at hfix
    exact hfix.symm
  · have hy' : k * y * k⁻¹ ∉ Set.range ι := by
      rintro ⟨x, hx⟩
      apply hy
      refine ⟨conj k⁻¹ x, ?_⟩
      rw [hconj, hx]
      group
    rw [embedded_coeff_zero ι _ _ hy', embedded_coeff_zero ι _ _ hy]

include hconj in
theorem embeddedResidueMatch_mem_orbit {χ : basis.index} {θ₀ θ : localBasis.index}
    (h₀ : EmbeddedResidueMatch basis localBasis ideal ι hι χ θ₀)
    (h : EmbeddedResidueMatch basis localBasis ideal ι hι χ θ) :
    θ ∈ orbitLabels localBasis ideal conj θ₀ := by
  let a : embeddedCommonCentralSubring (localizedComplexIntegerRing ideal) ι :=
    ⟨orbitIdempotent localBasis ideal conj θ₀,
      orbitIdempotent_mem localBasis ideal ι hι conj hconj θ₀⟩
  have hself : θ₀ ∈ orbitLabels localBasis ideal conj θ₀ := by
    rw [mem_orbitLabels_iff]
    refine ⟨1, θ₀, fun x => ?_, sameCoefficientBlock_refl _ _ _⟩
    rw [embedded_conj_one_apply ι hι conj hconj]
  have hvalue : ∀ θ', centralCharacterResidueHom localBasis ideal θ' a.val =
      if θ' ∈ orbitLabels localBasis ideal conj θ₀ then 1 else 0 := fun θ' =>
    centralCharacterResidueHom_subset localBasis ideal _
      (orbitLabels_admissible localBasis ideal conj θ₀) θ'
  have h1 := hvalue θ₀
  rw [ite_eq_left hself, h₀ a, ← h a, hvalue θ] at h1
  by_contra hnot
  rw [ite_eq_right hnot] at h1
  exact zero_ne_one h1

include hconj in
theorem embeddedResidueMatch_of_mem_orbit {χ : basis.index} {θ₀ θ : localBasis.index}
    (h₀ : EmbeddedResidueMatch basis localBasis ideal ι hι χ θ₀)
    (hθ : θ ∈ orbitLabels localBasis ideal conj θ₀) :
    EmbeddedResidueMatch basis localBasis ideal ι hι χ θ := by
  rw [mem_orbitLabels_iff] at hθ
  obtain ⟨k, θ', hθ', hsame⟩ := hθ
  exact embeddedResidueMatch_of_same basis localBasis ideal ι hι hsame
    ((embeddedResidueMatch_transport basis localBasis ideal ι hι conj hconj k hθ').mp h₀)

include hconj in
theorem embedded_block_orbits
    (hdetermined : ∀ z : centralCoefficientSubring (G := K) (localizedComplexIntegerRing ideal),
      ∃ a : embeddedCommonCentralSubring (localizedComplexIntegerRing ideal) ι, ∀ χ : basis.index,
        centralCharacterResidueHom basis ideal χ z =
          centralCharacterResidueHom basis ideal χ (embeddedCommonCentralInclusion _ ι hι a)) :
    (∀ (k : K) (θ : localBasis.index), ∃ θ', LabelTransport localBasis localBasis (conj k) θ θ') ∧
    (∀ (k : K) (θ₁ θ₂ θ₁' θ₂' : localBasis.index),
      LabelTransport localBasis localBasis (conj k) θ₁ θ₁' →
      LabelTransport localBasis localBasis (conj k) θ₂ θ₂' →
      (sameCoefficientBlock localBasis (localizedComplexIntegerRing ideal) θ₁ θ₂ ↔
        sameCoefficientBlock localBasis (localizedComplexIntegerRing ideal) θ₁' θ₂')) ∧
    (∀ χ : basis.index, (∃ θ, EmbeddedResidueMatch basis localBasis ideal ι hι χ θ) ∧
      ∀ θ₀, EmbeddedResidueMatch basis localBasis ideal ι hι χ θ₀ → ∀ θ,
        (EmbeddedResidueMatch basis localBasis ideal ι hι χ θ ↔
          ∃ k θ', LabelTransport localBasis localBasis (conj k) θ₀ θ' ∧
            sameCoefficientBlock localBasis (localizedComplexIntegerRing ideal) θ' θ)) ∧
    (∀ θ : localBasis.index, ∃ χ, EmbeddedResidueMatch basis localBasis ideal ι hι χ θ) ∧
    (∀ (χ₁ χ₂ : basis.index) (θ : localBasis.index),
      EmbeddedResidueMatch basis localBasis ideal ι hι χ₁ θ →
      EmbeddedResidueMatch basis localBasis ideal ι hι χ₂ θ →
      sameCoefficientBlock basis (localizedComplexIntegerRing ideal) χ₁ χ₂) ∧
    (∀ χ₁ χ₂ : basis.index, sameCoefficientBlock basis (localizedComplexIntegerRing ideal) χ₁ χ₂ →
      ∀ θ, EmbeddedResidueMatch basis localBasis ideal ι hι χ₁ θ ↔
        EmbeddedResidueMatch basis localBasis ideal ι hι χ₂ θ) := by
  refine ⟨fun k θ => labelTransport_exists localBasis localBasis (conj k) θ,
    fun k θ₁ θ₂ θ₁' θ₂' h₁ h₂ =>
      sameCoefficientBlock_labelTransport_iff localBasis localBasis ideal (conj k) h₁ h₂,
    fun χ => ⟨embeddedResidueMatch_restriction_exists basis localBasis ideal ι hι χ,
      fun θ₀ h₀ θ => ?_⟩,
    embeddedResidueMatch_extension_exists basis localBasis ideal ι hι,
    fun χ₁ χ₂ θ h₁ h₂ =>
      embeddedResidueMatch_injective basis localBasis ideal ι hι hdetermined h₁ h₂,
    fun χ₁ χ₂ hsame θ => embeddedResidueMatch_iff_of_same basis localBasis ideal ι hι hsame θ⟩
  rw [← mem_orbitLabels_iff localBasis ideal conj θ₀ θ]
  exact ⟨embeddedResidueMatch_mem_orbit basis localBasis ideal ι hι conj hconj h₀,
    embeddedResidueMatch_of_mem_orbit basis localBasis ideal ι hι conj hconj h₀⟩

end Embedded

section Conjugation

variable {G : Type*} [Group G]

@[expose] def centralizerConjugation (Q : Subgroup G) (h : G)
    (hh : h ∈ Subgroup.normalizer (Q : Set G)) :
    Subgroup.centralizer (Q : Set G) ≃* Subgroup.centralizer (Q : Set G) where
  toFun x := ⟨h * x * h⁻¹, (centralizer_conjugation_mem_iff Q h x hh).mpr x.property⟩
  invFun x := ⟨h⁻¹ * x * h, by
    have hmem := (centralizer_conjugation_mem_iff Q h⁻¹ x
      ((Subgroup.normalizer (Q : Set G)).inv_mem hh)).mpr x.property
    simpa only [inv_inv] using hmem⟩
  left_inv x := Subtype.ext (by dsimp; group)
  right_inv x := Subtype.ext (by dsimp; group)
  map_mul' x y := Subtype.ext (by dsimp; group)

theorem centralizerConjugation_apply (Q : Subgroup G) (h : G)
    (hh : h ∈ Subgroup.normalizer (Q : Set G)) (x : Subgroup.centralizer (Q : Set G)) :
    (centralizerConjugation Q h hh x : G) = h * x * h⁻¹ := rfl

@[expose] def normalCentralizerConj (P : Subgroup G) [P.Normal] (h : G) :
    Subgroup.centralizer (P : Set G) ≃* Subgroup.centralizer (P : Set G) :=
  centralizerConjugation P h ((Subgroup.normalizer_eq_top P) ▸ Subgroup.mem_top h)

theorem normalCentralizerConj_apply (P : Subgroup G) [P.Normal] (h : G)
    (x : Subgroup.centralizer (P : Set G)) : (normalCentralizerConj P h x : G) = h * x * h⁻¹ := rfl

end Conjugation

end BlockOrbits

open BlockOrbits

section Normal

variable {H : Type*} [Group H] [Fintype H]

@[expose] def NormalCentralizerResidueMatch (basis : FiniteIrreducibleCharacterBasis H)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal] (P : Subgroup H)
    (localBasis : FiniteIrreducibleCharacterBasis (Subgroup.centralizer (P : Set H)))
    (χ : basis.index) (θ : localBasis.index) : Prop :=
  ∀ a : commonCentralCoefficientSubring (localizedComplexIntegerRing ideal)
      (Subgroup.centralizer (P : Set H)),
    centralCharacterResidueHom localBasis ideal θ a.val =
      centralCharacterResidueHom basis ideal χ (commonCentralCoefficientInclusion _ _ a)

theorem normalCentralizer_residue_determined (basis : FiniteIrreducibleCharacterBasis H)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal] (p : ℕ) [Fact p.Prime]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) p] (P : Subgroup H) [P.Normal] (hP : IsPGroup p P)
    (z : centralCoefficientSubring (G := H) (localizedComplexIntegerRing ideal)) :
    ∃ a : commonCentralCoefficientSubring (localizedComplexIntegerRing ideal)
        (Subgroup.centralizer (P : Set H)), ∀ χ : basis.index,
      centralCharacterResidueHom basis ideal χ z =
        centralCharacterResidueHom basis ideal χ (commonCentralCoefficientInclusion _ _ a) := by
  refine ⟨⟨centralSubgroupCoefficientProjection _ (Subgroup.centralizer (P : Set H)) z,
    normalCentralizer_projection_common _ P z⟩, fun χ => ?_⟩
  apply normal_p_central_residue_determined_by_projection basis ideal p P hP
  rw [commonCentralCoefficientInclusion_projection]

theorem normal_centralizer_block_orbits (basis : FiniteIrreducibleCharacterBasis H)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal] (p : ℕ) [Fact p.Prime]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) p] (P : Subgroup H) [P.Normal] (hP : IsPGroup p P)
    (localBasis : FiniteIrreducibleCharacterBasis (Subgroup.centralizer (P : Set H))) :
    (∀ (h : H) (θ : localBasis.index),
      ∃ θ', LabelTransport localBasis localBasis (normalCentralizerConj P h) θ θ') ∧
    (∀ (h : H) (θ₁ θ₂ θ₁' θ₂' : localBasis.index),
      LabelTransport localBasis localBasis (normalCentralizerConj P h) θ₁ θ₁' →
      LabelTransport localBasis localBasis (normalCentralizerConj P h) θ₂ θ₂' →
      (sameCoefficientBlock localBasis (localizedComplexIntegerRing ideal) θ₁ θ₂ ↔
        sameCoefficientBlock localBasis (localizedComplexIntegerRing ideal) θ₁' θ₂')) ∧
    (∀ χ : basis.index, (∃ θ, NormalCentralizerResidueMatch basis ideal P localBasis χ θ) ∧
      ∀ θ₀, NormalCentralizerResidueMatch basis ideal P localBasis χ θ₀ → ∀ θ,
        (NormalCentralizerResidueMatch basis ideal P localBasis χ θ ↔
          ∃ (h : H) (θ' : localBasis.index),
            LabelTransport localBasis localBasis (normalCentralizerConj P h) θ₀ θ' ∧
            sameCoefficientBlock localBasis (localizedComplexIntegerRing ideal) θ' θ)) ∧
    (∀ θ : localBasis.index, ∃ χ, NormalCentralizerResidueMatch basis ideal P localBasis χ θ) ∧
    (∀ (χ₁ χ₂ : basis.index) (θ : localBasis.index),
      NormalCentralizerResidueMatch basis ideal P localBasis χ₁ θ →
      NormalCentralizerResidueMatch basis ideal P localBasis χ₂ θ →
      sameCoefficientBlock basis (localizedComplexIntegerRing ideal) χ₁ χ₂) ∧
    (∀ χ₁ χ₂ : basis.index, sameCoefficientBlock basis (localizedComplexIntegerRing ideal) χ₁ χ₂ →
      ∀ θ, NormalCentralizerResidueMatch basis ideal P localBasis χ₁ θ ↔
        NormalCentralizerResidueMatch basis ideal P localBasis χ₂ θ) :=
  embedded_block_orbits basis localBasis ideal (Subgroup.centralizer (P : Set H)).subtype
    (Subgroup.subtype_injective _) (normalCentralizerConj P) (fun _ _ => rfl)
    (normalCentralizer_residue_determined basis ideal p P hP)

theorem normalCentralizer_brauerProjection_eq (ring : Subring ℂ) (P : Subgroup H)
    (z : centralCoefficientSubring (G := H) ring) :
    centralNormalizerCoefficientProjection ring P (Subgroup.centralizer (P : Set H)) le_rfl
      (Subgroup.centralizer_le_normalizer _) z =
        centralSubgroupCoefficientProjection ring (Subgroup.centralizer (P : Set H)) z := by
  apply Subtype.ext
  ext c
  rw [centralNormalizerCoefficientProjection_coeff, ite_eq_left c.property]
  exact (subgroupCoefficientProjection_coeff _ z.val c).symm

theorem normalCentralizer_brauer_eq_iff_match (basis : FiniteIrreducibleCharacterBasis H)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal] (p : ℕ) [Fact p.Prime]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) p] (P : Subgroup H) [P.Normal] (hP : IsPGroup p P)
    (localBasis : FiniteIrreducibleCharacterBasis (Subgroup.centralizer (P : Set H)))
    (χ : basis.index) (θ : localBasis.index) :
    brauerNormalizerCharacterResidueHom ideal p P hP (Subgroup.centralizer (P : Set H)) le_rfl
        (Subgroup.centralizer_le_normalizer _) localBasis θ =
      centralCharacterResidueHom basis ideal χ ↔
    NormalCentralizerResidueMatch basis ideal P localBasis χ θ := by
  constructor
  · intro hequal a
    have hvalue := congrArg (fun hom => hom (commonCentralCoefficientInclusion _ _ a)) hequal
    change centralCharacterResidueHom localBasis ideal θ
      (centralNormalizerCoefficientProjection _ P _ le_rfl _ _) = _ at hvalue
    rw [normalCentralizer_brauerProjection_eq, commonCentralCoefficientInclusion_projection]
      at hvalue
    exact hvalue
  · intro hmatch
    apply RingHom.ext
    intro z
    change centralCharacterResidueHom localBasis ideal θ
      (centralNormalizerCoefficientProjection _ P _ le_rfl _ z) = _
    rw [normalCentralizer_brauerProjection_eq]
    have hdetermined := normal_p_central_residue_determined_by_projection basis ideal p P hP z
      (commonCentralCoefficientInclusion _ _ ⟨centralSubgroupCoefficientProjection _
        (Subgroup.centralizer (P : Set H)) z, normalCentralizer_projection_common _ P z⟩)
      (by rw [commonCentralCoefficientInclusion_projection]) χ
    rw [hdetermined]
    exact hmatch ⟨_, normalCentralizer_projection_common _ P z⟩

theorem normal_p_centralizer_brauer_fibers_are_block_orbits
    (basis : FiniteIrreducibleCharacterBasis H) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] (p : ℕ) [Fact p.Prime] [CharP (ComplexAlgebraicIntegers ⧸ ideal) p]
    (P : Subgroup H) [P.Normal] (hP : IsPGroup p P)
    (localBasis : FiniteIrreducibleCharacterBasis (Subgroup.centralizer (P : Set H))) :
    (∀ θ : localBasis.index, ∃ χ : basis.index,
      brauerNormalizerCharacterResidueHom ideal p P hP (Subgroup.centralizer (P : Set H)) le_rfl
        (Subgroup.centralizer_le_normalizer _) localBasis θ =
          centralCharacterResidueHom basis ideal χ) ∧
    (∀ χ : basis.index, ∃ θ : localBasis.index,
      brauerNormalizerCharacterResidueHom ideal p P hP (Subgroup.centralizer (P : Set H)) le_rfl
        (Subgroup.centralizer_le_normalizer _) localBasis θ =
          centralCharacterResidueHom basis ideal χ) ∧
    (∀ θ θ₂ : localBasis.index,
      brauerNormalizerCharacterResidueHom ideal p P hP (Subgroup.centralizer (P : Set H)) le_rfl
          (Subgroup.centralizer_le_normalizer _) localBasis θ =
        brauerNormalizerCharacterResidueHom ideal p P hP (Subgroup.centralizer (P : Set H)) le_rfl
          (Subgroup.centralizer_le_normalizer _) localBasis θ₂ ↔
      ∃ (h : H) (θ' : localBasis.index),
        LabelTransport localBasis localBasis (normalCentralizerConj P h) θ θ' ∧
        sameCoefficientBlock localBasis (localizedComplexIntegerRing ideal) θ' θ₂) := by
  obtain ⟨-, -, horbit, hextension, hinjective, -⟩ :=
    normal_centralizer_block_orbits basis ideal p P hP localBasis
  have himage : ∀ θ : localBasis.index, ∃ χ : basis.index,
      brauerNormalizerCharacterResidueHom ideal p P hP (Subgroup.centralizer (P : Set H)) le_rfl
        (Subgroup.centralizer_le_normalizer _) localBasis θ =
          centralCharacterResidueHom basis ideal χ :=
    fun θ => brauerNormalizer_block_image_exists basis ideal p P hP _ le_rfl
      (Subgroup.centralizer_le_normalizer _) localBasis θ
  refine ⟨himage, fun χ => ?_, fun θ θ₂ => ?_⟩
  · obtain ⟨θ, hθ⟩ := (horbit χ).1
    exact ⟨θ, (normalCentralizer_brauer_eq_iff_match basis ideal p P hP localBasis χ θ).mpr hθ⟩
  · obtain ⟨χ, hχ⟩ := himage θ
    have hθ := (normalCentralizer_brauer_eq_iff_match basis ideal p P hP localBasis χ θ).mp hχ
    rw [hχ, eq_comm, normalCentralizer_brauer_eq_iff_match basis ideal p P hP localBasis χ θ₂]
    exact (horbit χ).2 θ hθ θ₂

end Normal

section External

variable {G : Type*} [Group G] [Fintype G]

@[expose] def ExternalResidueMatch (Q H : Subgroup G)
    (hCH : Subgroup.centralizer (Q : Set G) ≤ H) (basis : FiniteIrreducibleCharacterBasis H)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    (localBasis : FiniteIrreducibleCharacterBasis (Subgroup.centralizer (Q : Set G)))
    (χ : basis.index) (θ : localBasis.index) : Prop :=
  ∀ a : externalCommonCentralCoefficientSubring (localizedComplexIntegerRing ideal) Q H hCH,
    centralCharacterResidueHom localBasis ideal θ a.val =
      centralCharacterResidueHom basis ideal χ
        (externalCommonCentralCoefficientInclusion _ Q H hCH a)

@[expose] noncomputable def externalRestrictionElement (Q H : Subgroup G)
    (hCH : Subgroup.centralizer (Q : Set G) ≤ H) (z : MonoidAlgebra ℂ H) :
    MonoidAlgebra ℂ (Subgroup.centralizer (Q : Set G)) :=
  MonoidAlgebra.ofCoeff
    (Finsupp.equivFunOnFinite.symm fun c => z.coeff (Subgroup.inclusion hCH c))

theorem externalRestrictionElement_coeff (Q H : Subgroup G)
    (hCH : Subgroup.centralizer (Q : Set G) ≤ H) (z : MonoidAlgebra ℂ H)
    (c : Subgroup.centralizer (Q : Set G)) :
    (externalRestrictionElement Q H hCH z).coeff c = z.coeff (Subgroup.inclusion hCH c) := rfl

theorem externalRestrictionElement_mem (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    (Q H : Subgroup G) (hCH : Subgroup.centralizer (Q : Set G) ≤ H)
    (z : centralCoefficientSubring (G := H) (localizedComplexIntegerRing ideal)) :
    externalRestrictionElement Q H hCH z.val ∈ centralCoefficientSubring
      (G := Subgroup.centralizer (Q : Set G)) (localizedComplexIntegerRing ideal) := by
  have hz : ∀ y k : H, z.val.coeff (k * y * k⁻¹) = z.val.coeff y := fun y k =>
    central_groupAlgebra_coeff_conjugation z.val (centralCoefficientSubring_commutes _ z) y k
  constructor
  · intro c
    rw [externalRestrictionElement_coeff]
    exact centralCoefficientSubring_coefficients _ z _
  · apply Subring.mem_center_iff.mpr
    intro other
    apply Commute.symm
    apply groupAlgebra_central_of_coeff_conjugation
    intro x c
    rw [externalRestrictionElement_coeff, externalRestrictionElement_coeff]
    have hmap : Subgroup.inclusion hCH (c * x * c⁻¹) =
        Subgroup.inclusion hCH c * Subgroup.inclusion hCH x * (Subgroup.inclusion hCH c)⁻¹ := by
      rw [map_mul (Subgroup.inclusion hCH), map_mul (Subgroup.inclusion hCH),
        map_inv (Subgroup.inclusion hCH)]
    rw [hmap, hz]

theorem externalRestrictionElement_common (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] (Q H : Subgroup G) (hCH : Subgroup.centralizer (Q : Set G) ≤ H)
    (hHN : H ≤ Subgroup.normalizer (Q : Set G))
    (z : centralCoefficientSubring (G := H) (localizedComplexIntegerRing ideal)) :
    (⟨externalRestrictionElement Q H hCH z.val, externalRestrictionElement_mem ideal Q H hCH z⟩ :
      centralCoefficientSubring (G := Subgroup.centralizer (Q : Set G))
        (localizedComplexIntegerRing ideal)) ∈
      externalCommonCentralCoefficientSubring (localizedComplexIntegerRing ideal) Q H hCH := by
  have hι : Function.Injective (Subgroup.inclusion hCH) := Subgroup.inclusion_injective hCH
  have hz : ∀ y k : H, z.val.coeff (k * y * k⁻¹) = z.val.coeff y := fun y k =>
    central_groupAlgebra_coeff_conjugation z.val (centralCoefficientSubring_commutes _ z) y k
  have hconj : ∀ (k : H) (x : Subgroup.centralizer (Q : Set G)),
      Subgroup.inclusion hCH (centralizerConjugation Q k (hHN k.property) x) =
        k * Subgroup.inclusion hCH x * k⁻¹ := fun _ _ => rfl
  change MonoidAlgebra.mapDomainRingHom ℂ (Subgroup.inclusion hCH)
      (externalRestrictionElement Q H hCH z.val) ∈ Subring.center (MonoidAlgebra ℂ H)
  apply Subring.mem_center_iff.mpr
  intro other
  apply Commute.symm
  apply groupAlgebra_central_of_coeff_conjugation
  intro y k
  by_cases hy : y ∈ Set.range (Subgroup.inclusion hCH)
  · obtain ⟨x, rfl⟩ := hy
    rw [← hconj, embedded_coeff _ hι, embedded_coeff _ hι, externalRestrictionElement_coeff,
      externalRestrictionElement_coeff, hconj, hz]
  · have hy' : k * y * k⁻¹ ∉ Set.range (Subgroup.inclusion hCH) := by
      rintro ⟨x, hx⟩
      apply hy
      refine ⟨centralizerConjugation Q ((k⁻¹ : H) : G) (hHN (k⁻¹).property) x, ?_⟩
      rw [hconj, hx]
      group
    rw [embedded_coeff_zero _ _ _ hy', embedded_coeff_zero _ _ _ hy]

@[expose] noncomputable def externalCentralRestriction (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] (Q H : Subgroup G) (hCH : Subgroup.centralizer (Q : Set G) ≤ H)
    (hHN : H ≤ Subgroup.normalizer (Q : Set G))
    (z : centralCoefficientSubring (G := H) (localizedComplexIntegerRing ideal)) :
    externalCommonCentralCoefficientSubring (localizedComplexIntegerRing ideal) Q H hCH :=
  ⟨⟨externalRestrictionElement Q H hCH z.val, externalRestrictionElement_mem ideal Q H hCH z⟩,
    externalRestrictionElement_common ideal Q H hCH hHN z⟩

theorem externalCentralRestriction_coeff (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] (Q H : Subgroup G) (hCH : Subgroup.centralizer (Q : Set G) ≤ H)
    (hHN : H ≤ Subgroup.normalizer (Q : Set G))
    (z : centralCoefficientSubring (G := H) (localizedComplexIntegerRing ideal))
    (c : Subgroup.centralizer (Q : Set G)) :
    (externalCentralRestriction ideal Q H hCH hHN z).val.val.coeff c =
      z.val.coeff (Subgroup.inclusion hCH c) := rfl

theorem externalCentralRestriction_residue (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] (p : ℕ) [Fact p.Prime] [CharP (ComplexAlgebraicIntegers ⧸ ideal) p]
    (Q H : Subgroup G) (hQ : IsPGroup p Q) (hQH : Q ≤ H)
    (hCH : Subgroup.centralizer (Q : Set G) ≤ H) (hHN : H ≤ Subgroup.normalizer (Q : Set G))
    (basis : FiniteIrreducibleCharacterBasis H)
    (z : centralCoefficientSubring (G := H) (localizedComplexIntegerRing ideal))
    (χ : basis.index) :
    centralCharacterResidueHom basis ideal χ z =
      centralCharacterResidueHom basis ideal χ (externalCommonCentralCoefficientInclusion _ Q H hCH
        (externalCentralRestriction ideal Q H hCH hHN z)) := by
  have hι : Function.Injective (Subgroup.inclusion hCH) := Subgroup.inclusion_injective hCH
  let : (Q.subgroupOf H).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hHN
  apply normal_p_central_residue_determined_by_projection basis ideal p (Q.subgroupOf H)
    hQ.comap_subtype
  apply Subtype.ext
  ext w
  rw [centralSubgroupCoefficientProjection_val, centralSubgroupCoefficientProjection_val,
    subgroupCoefficientProjection_coeff, subgroupCoefficientProjection_coeff]
  have hw : ((w : H) : G) ∈ Subgroup.centralizer (Q : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have hcomm := Subgroup.mem_centralizer_iff.mp w.property (⟨q, hQH hq⟩ : H) hq
    exact congrArg Subtype.val hcomm
  have hequal : (w : H) = Subgroup.inclusion hCH ⟨w, hw⟩ := rfl
  change z.val.coeff (w : H) = (MonoidAlgebra.mapDomainRingHom ℂ (Subgroup.inclusion hCH)
    (externalRestrictionElement Q H hCH z.val)).coeff (w : H)
  rw [hequal, embedded_coeff _ hι, externalRestrictionElement_coeff]

theorem external_residue_determined (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    (p : ℕ) [Fact p.Prime] [CharP (ComplexAlgebraicIntegers ⧸ ideal) p] (Q H : Subgroup G)
    (hQ : IsPGroup p Q) (hQH : Q ≤ H) (hCH : Subgroup.centralizer (Q : Set G) ≤ H)
    (hHN : H ≤ Subgroup.normalizer (Q : Set G)) (basis : FiniteIrreducibleCharacterBasis H)
    (z : centralCoefficientSubring (G := H) (localizedComplexIntegerRing ideal)) :
    ∃ a : externalCommonCentralCoefficientSubring (localizedComplexIntegerRing ideal) Q H hCH,
      ∀ χ : basis.index, centralCharacterResidueHom basis ideal χ z =
        centralCharacterResidueHom basis ideal χ
          (externalCommonCentralCoefficientInclusion _ Q H hCH a) :=
  ⟨externalCentralRestriction ideal Q H hCH hHN z,
    externalCentralRestriction_residue ideal p Q H hQ hQH hCH hHN basis z⟩

theorem external_block_orbits (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    (p : ℕ) [Fact p.Prime] [CharP (ComplexAlgebraicIntegers ⧸ ideal) p] (Q H : Subgroup G)
    (hQ : IsPGroup p Q) (hQH : Q ≤ H) (hCH : Subgroup.centralizer (Q : Set G) ≤ H)
    (hHN : H ≤ Subgroup.normalizer (Q : Set G)) (basis : FiniteIrreducibleCharacterBasis H)
    (localBasis : FiniteIrreducibleCharacterBasis (Subgroup.centralizer (Q : Set G))) :
    (∀ (h : H) (θ : localBasis.index),
      ∃ θ', LabelTransport localBasis localBasis
        (centralizerConjugation Q h (hHN h.property)) θ θ') ∧
    (∀ (h : H) (θ₁ θ₂ θ₁' θ₂' : localBasis.index),
      LabelTransport localBasis localBasis (centralizerConjugation Q h (hHN h.property)) θ₁ θ₁' →
      LabelTransport localBasis localBasis (centralizerConjugation Q h (hHN h.property)) θ₂ θ₂' →
      (sameCoefficientBlock localBasis (localizedComplexIntegerRing ideal) θ₁ θ₂ ↔
        sameCoefficientBlock localBasis (localizedComplexIntegerRing ideal) θ₁' θ₂')) ∧
    (∀ χ : basis.index, (∃ θ, ExternalResidueMatch Q H hCH basis ideal localBasis χ θ) ∧
      ∀ θ₀, ExternalResidueMatch Q H hCH basis ideal localBasis χ θ₀ → ∀ θ,
        (ExternalResidueMatch Q H hCH basis ideal localBasis χ θ ↔
          ∃ (h : H) (θ' : localBasis.index),
            LabelTransport localBasis localBasis
              (centralizerConjugation Q h (hHN h.property)) θ₀ θ' ∧
            sameCoefficientBlock localBasis (localizedComplexIntegerRing ideal) θ' θ)) ∧
    (∀ θ : localBasis.index, ∃ χ, ExternalResidueMatch Q H hCH basis ideal localBasis χ θ) ∧
    (∀ (χ₁ χ₂ : basis.index) (θ : localBasis.index),
      ExternalResidueMatch Q H hCH basis ideal localBasis χ₁ θ →
      ExternalResidueMatch Q H hCH basis ideal localBasis χ₂ θ →
      sameCoefficientBlock basis (localizedComplexIntegerRing ideal) χ₁ χ₂) ∧
    (∀ χ₁ χ₂ : basis.index, sameCoefficientBlock basis (localizedComplexIntegerRing ideal) χ₁ χ₂ →
      ∀ θ, ExternalResidueMatch Q H hCH basis ideal localBasis χ₁ θ ↔
        ExternalResidueMatch Q H hCH basis ideal localBasis χ₂ θ) :=
  embedded_block_orbits basis localBasis ideal (Subgroup.inclusion hCH)
    (Subgroup.inclusion_injective hCH) (fun h => centralizerConjugation Q h (hHN h.property))
    (fun _ _ => rfl) (external_residue_determined ideal p Q H hQ hQH hCH hHN basis)

theorem external_brauer_apply_of_match (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    (p : ℕ) [Fact p.Prime] [CharP (ComplexAlgebraicIntegers ⧸ ideal) p] (Q H : Subgroup G)
    (hQ : IsPGroup p Q) (hCH : Subgroup.centralizer (Q : Set G) ≤ H)
    (hHN : H ≤ Subgroup.normalizer (Q : Set G)) (basis : FiniteIrreducibleCharacterBasis H)
    (localBasis : FiniteIrreducibleCharacterBasis (Subgroup.centralizer (Q : Set G)))
    {χ : basis.index} {θ : localBasis.index}
    (hmatch : ExternalResidueMatch Q H hCH basis ideal localBasis χ θ)
    (z : centralCoefficientSubring (G := G) (localizedComplexIntegerRing ideal)) :
    brauerNormalizerCharacterResidueHom ideal p Q hQ H hCH hHN basis χ z =
      centralCharacterResidueHom localBasis ideal θ
        (centralSubgroupCoefficientProjection _ (Subgroup.centralizer (Q : Set G)) z) := by
  have h := hmatch ⟨centralSubgroupCoefficientProjection _ (Subgroup.centralizer (Q : Set G)) z,
    externalCommonCentralCoefficientProjection_mem _ Q H hCH hHN z⟩
  rw [externalCommonCentralCoefficientProjection_inclusion _ Q H hCH hHN z] at h
  exact h.symm

end External

end CFSG.Wreathed
