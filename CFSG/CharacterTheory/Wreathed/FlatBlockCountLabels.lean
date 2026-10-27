module

public import CFSG.CharacterTheory.Wreathed.FlatWreathedBlock

public section

open scoped BigOperators Classical

namespace CFSG.Wreathed

open CFSG.TwoRankLowerBound.Helpers CFSG.Wreathed.FullDefectLabels
  CFSG.Wreathed.BaseFourCentralizerStructure

variable {G : Type*} [Group G] [Fintype G]

@[expose] noncomputable def flatWreathedBlocks (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] {n : ℕ} (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) : Finset (Finset basis.index) :=
  (Finset.univ.filter (FlatWreathedBlock basis ideal S e)).image
    (coefficientBlock basis (localizedComplexIntegerRing ideal))

section Blocks

variable {basis : FiniteIrreducibleCharacterBasis G} {ideal : Ideal ComplexAlgebraicIntegers}
  [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] {n : ℕ} {S : Sylow 2 G}
  {e : S ≃* Wreath (2 ^ n)}

theorem mem_flatWreathedBlocks {𝔅 : Finset basis.index} :
    𝔅 ∈ flatWreathedBlocks basis ideal S e ↔ ∃ B, FlatWreathedBlock basis ideal S e B ∧
      coefficientBlock basis (localizedComplexIntegerRing ideal) B = 𝔅 := by
  simp only [flatWreathedBlocks, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]

theorem FlatWreathedBlock.of_residue_eq {B B' : basis.index}
    (hres : centralCharacterResidueHom basis ideal B = centralCharacterResidueHom basis ideal B')
    (hflat : FlatWreathedBlock basis ideal S e B') : FlatWreathedBlock basis ideal S e B := by
  obtain ⟨hdef, eb, θ, nb, θhat, hθ, hB, hrest⟩ := hflat
  refine ⟨?_, eb, θ, nb, θhat, hθ, hB.trans hres.symm, hrest⟩
  unfold coefficientBlockDefect at hdef ⊢
  rw [hres]
  exact hdef

theorem FlatWreathedBlock.of_mem {𝔅 : Finset basis.index}
    (h𝔅 : 𝔅 ∈ flatWreathedBlocks basis ideal S e) {B : basis.index} (hB : B ∈ 𝔅) :
    FlatWreathedBlock basis ideal S e B := by
  obtain ⟨B₀, hflat, rfl⟩ := mem_flatWreathedBlocks.mp h𝔅
  have hsame := (coefficientBlock_mem_iff _ _ _ _).mp hB
  rw [sameCoefficientBlock_iff_centralCharacterResidueHom_eq] at hsame
  exact FlatWreathedBlock.of_residue_eq hsame.symm hflat

end Blocks

theorem flatWreathedBlock_iff (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] {n : ℕ} (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) {B : basis.index}
    (eb : FiniteIrreducibleCharacterBasis
      (ambientOddCore (Subgroup.centralizer ((S : Subgroup G) : Set G)))) (θ : eb.index)
    (nb : FiniteIrreducibleCharacterBasis (Subgroup.normalizer ((S : Subgroup G) : Set G)))
    (θhat : nb.index) (hθ : InflatedLabel (oddCore_le_normalizer S) nb eb θ θhat)
    (hB : brauerNormalizerCharacterResidueHom ideal 2 (S : Subgroup G) S.isPGroup'
        (Subgroup.normalizer ((S : Subgroup G) : Set G)) (Subgroup.centralizer_le_normalizer _)
        le_rfl nb θhat = centralCharacterResidueHom basis ideal B) :
    FlatWreathedBlock basis ideal S e B ↔
      ∃ θt : Subgroup.centralizer ((S : Subgroup G) : Set G) → ℂ,
        (∀ (c : Subgroup.centralizer ((S : Subgroup G) : Set G)) (z : G)
          (y : ambientOddCore (Subgroup.centralizer ((S : Subgroup G) : Set G))),
          z ∈ Subgroup.zpowers (wreathModelHom S e (Original.s (2 ^ n)) *
            wreathModelHom S e (Original.t (2 ^ n))) → (c : G) = z * y →
            θt c = (eb.representation θ).character y) ∧
        ∃ ψ, CompatibleCentralizerFamily 2 (S : Subgroup G) θt ψ := by
  have ha : wreathModelHom S e (Original.a (2 ^ n)) =
      wreathModelHom S e (Original.s (2 ^ n)) * wreathModelHom S e (Original.t (2 ^ n)) :=
    map_mul _ _ _
  constructor
  · intro hflat
    obtain ⟨-, eb', θ', nb', θhat', hθ', hB', θt', hθt', ψ, hψ⟩ := hflat
    have hchar := canonicalLabel_character_eq basis ideal hn S e eb θ nb θhat hθ hB eb' θ' nb'
      θhat' hθ' hB'
    refine ⟨θt', fun c z y hz hc => ?_, ψ, hψ⟩
    rw [hθt' c z y (by rwa [ha]) hc, hchar]
  · rintro ⟨θt, hθt, ψ, hψ⟩
    exact FlatWreathedBlock.of_family basis ideal hn S e eb θ nb θhat hθ hB θt
      (fun c z y hz hc => hθt c z y (by rwa [← ha]) hc) hψ

theorem exists_canonicalLabel_of_mem_flatWreathedBlocks (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] {n : ℕ} (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n))
    (eb : FiniteIrreducibleCharacterBasis
      (ambientOddCore (Subgroup.centralizer ((S : Subgroup G) : Set G))))
    (nb : FiniteIrreducibleCharacterBasis (Subgroup.normalizer ((S : Subgroup G) : Set G)))
    {𝔅 : Finset basis.index} (h𝔅 : 𝔅 ∈ flatWreathedBlocks basis ideal S e) {B : basis.index}
    (hB : B ∈ 𝔅) :
    ∃ (θ : eb.index) (θhat : nb.index), InflatedLabel (oddCore_le_normalizer S) nb eb θ θhat ∧
      brauerNormalizerCharacterResidueHom ideal 2 (S : Subgroup G) S.isPGroup'
          (Subgroup.normalizer ((S : Subgroup G) : Set G))
          (Subgroup.centralizer_le_normalizer _) le_rfl nb θhat =
        centralCharacterResidueHom basis ideal B := by
  obtain ⟨principal, hprincipal⟩ := finiteIrreducibleCharacterBasis_contains_irreducible basis
    (principalFiniteComplexRepresentation G) (principalFiniteComplexRepresentation_isIrreducible G)
  rw [principalFiniteComplexRepresentation_character] at hprincipal
  exact (full_defect_block_canonical_sylow_centralizer_labels basis ideal n hn S e nb eb principal
    hprincipal).2.2.2.2.2.2.1 B (FlatWreathedBlock.of_mem h𝔅 hB).defect

theorem exists_equiv_flatWreathedBlocks (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] {n : ℕ} (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n))
    (eb : FiniteIrreducibleCharacterBasis
      (ambientOddCore (Subgroup.centralizer ((S : Subgroup G) : Set G))))
    (nb : FiniteIrreducibleCharacterBasis (Subgroup.normalizer ((S : Subgroup G) : Set G)))
    (Ξ : Set eb.index)
    (hΞ : Ξ = {θ | ∃ θt : Subgroup.centralizer ((S : Subgroup G) : Set G) → ℂ,
      (∀ (c : Subgroup.centralizer ((S : Subgroup G) : Set G)) (z : G)
        (y : ambientOddCore (Subgroup.centralizer ((S : Subgroup G) : Set G))),
        z ∈ Subgroup.zpowers (wreathModelHom S e (Original.s (2 ^ n)) *
          wreathModelHom S e (Original.t (2 ^ n))) → (c : G) = z * y →
          θt c = (eb.representation θ).character y) ∧
      ∃ ψ, CompatibleCentralizerFamily 2 (S : Subgroup G) θt ψ}) :
    ∃ g : Ξ ≃ flatWreathedBlocks basis ideal S e, ∀ (θ : Ξ) (B : basis.index),
      B ∈ (g θ : Finset basis.index) → ∀ (θ' : eb.index) (θhat' : nb.index),
        InflatedLabel (oddCore_le_normalizer S) nb eb θ' θhat' →
        brauerNormalizerCharacterResidueHom ideal 2 (S : Subgroup G) S.isPGroup'
            (Subgroup.normalizer ((S : Subgroup G) : Set G))
            (Subgroup.centralizer_le_normalizer _) le_rfl nb θhat' =
          centralCharacterResidueHom basis ideal B → θ' = θ := by
  have hmem : ∀ θ, θ ∈ Ξ ↔ ∃ θt : Subgroup.centralizer ((S : Subgroup G) : Set G) → ℂ,
      (∀ (c : Subgroup.centralizer ((S : Subgroup G) : Set G)) (z : G)
        (y : ambientOddCore (Subgroup.centralizer ((S : Subgroup G) : Set G))),
        z ∈ Subgroup.zpowers (wreathModelHom S e (Original.s (2 ^ n)) *
          wreathModelHom S e (Original.t (2 ^ n))) → (c : G) = z * y →
          θt c = (eb.representation θ).character y) ∧
      ∃ ψ, CompatibleCentralizerFamily 2 (S : Subgroup G) θt ψ := fun θ => by
    rw [hΞ, Set.mem_ofPred_eq]
  obtain ⟨principal, hprincipal⟩ := finiteIrreducibleCharacterBasis_contains_irreducible basis
    (principalFiniteComplexRepresentation G) (principalFiniteComplexRepresentation_isIrreducible G)
  rw [principalFiniteComplexRepresentation_character] at hprincipal
  obtain ⟨hinfl, -, -, -, -, hBex, hlabel, hinj, -⟩ :=
    full_defect_block_canonical_sylow_centralizer_labels basis ideal n hn S e nb eb principal
      hprincipal
  choose θhat hθhat using fun θ => (hinfl θ).exists
  choose B hBr hBdef using fun θ => hBex θ (θhat θ) (hθhat θ)
  have hflat : ∀ θ ∈ Ξ, FlatWreathedBlock basis ideal S e (B θ) := fun θ hθ =>
    (flatWreathedBlock_iff basis ideal hn S e eb θ nb (θhat θ) (hθhat θ) (hBr θ)).mpr
      ((hmem θ).mp hθ)
  let g : Ξ → flatWreathedBlocks basis ideal S e := fun θ =>
    ⟨coefficientBlock basis (localizedComplexIntegerRing ideal) (B θ),
      mem_flatWreathedBlocks.mpr ⟨B θ, hflat θ θ.2, rfl⟩⟩
  have hlab : ∀ (θ : Ξ) (B' : basis.index), B' ∈ (g θ : Finset basis.index) →
      ∀ (θ' : eb.index) (θhat' : nb.index),
        InflatedLabel (oddCore_le_normalizer S) nb eb θ' θhat' →
        brauerNormalizerCharacterResidueHom ideal 2 (S : Subgroup G) S.isPGroup'
            (Subgroup.normalizer ((S : Subgroup G) : Set G))
            (Subgroup.centralizer_le_normalizer _) le_rfl nb θhat' =
          centralCharacterResidueHom basis ideal B' → θ' = θ := by
    intro θ B' hB' θ' θhat' hθ' hBr'
    have hsame := (coefficientBlock_mem_iff _ _ _ _).mp hB'
    rw [sameCoefficientBlock_iff_centralCharacterResidueHom_eq] at hsame
    exact hinj θ' θ θhat' (θhat θ) hθ' (hθhat θ) (hBr'.trans (hsame.symm.trans (hBr θ).symm))
  have hbij : Function.Bijective g := by
    constructor
    · intro θ₁ θ₂ h
      apply Subtype.ext
      have h' : B θ₂ ∈ (g θ₁ : Finset basis.index) := by
        rw [h]
        exact coefficientBlock_self_mem _ _ _
      exact (hlab θ₁ (B θ₂) h' θ₂ (θhat θ₂) (hθhat θ₂) (hBr θ₂)).symm
    · rintro ⟨𝔅, h𝔅⟩
      obtain ⟨B₀, hB₀, rfl⟩ := mem_flatWreathedBlocks.mp h𝔅
      obtain ⟨θ, θh, hθ, hθBr⟩ := hlabel B₀ hB₀.defect
      have hθΞ : θ ∈ Ξ := (hmem θ).mpr
        ((flatWreathedBlock_iff basis ideal hn S e eb θ nb θh hθ hθBr).mp hB₀)
      refine ⟨⟨θ, hθΞ⟩, Subtype.ext ?_⟩
      have hθh : θhat θ = θh := (hinfl θ).unique (hθhat θ) hθ
      have hres : centralCharacterResidueHom basis ideal B₀ =
          centralCharacterResidueHom basis ideal (B θ) := by
        rw [← hθBr, ← hBr θ, hθh]
      exact coefficientBlock_eq_of_mem basis _ ((coefficientBlock_mem_iff _ _ _ _).mpr
        ((sameCoefficientBlock_iff_centralCharacterResidueHom_eq basis ideal _ _).mpr hres))
  exact ⟨Equiv.ofBijective g hbij, hlab⟩

end CFSG.Wreathed
