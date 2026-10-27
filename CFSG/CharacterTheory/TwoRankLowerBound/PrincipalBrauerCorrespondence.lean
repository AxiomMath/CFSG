module

public import CFSG.CharacterTheory.TwoRankLowerBound.RelativeCentralizerResidues
public import CFSG.CharacterTheory.TwoRankLowerBound.PrincipalBrauerDefectGrowth

public section

open scoped Classical Pointwise

namespace CFSG.TwoRankLowerBound.Helpers

theorem brauerNormalizer_principal_residue_preimage {group : Type*} [Group group] [Fintype group]
    (basis : FiniteIrreducibleCharacterBasis group)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    (prime : ℕ) [Fact prime.Prime] [CharP (ComplexAlgebraicIntegers ⧸ ideal) prime]
    (primary : Subgroup group) (hprimary : IsPGroup prime primary) (intermediate : Subgroup group)
    (hprimaryContains : primary ≤ intermediate)
    (hcontains : Subgroup.centralizer (primary : Set group) ≤ intermediate)
    (hnormalizes : intermediate ≤ Subgroup.normalizer (primary : Set group))
    (intermediateBasis : FiniteIrreducibleCharacterBasis intermediate)
    (principal : basis.index) (hprincipal : (basis.representation principal).character = 1)
    (intermediatePrincipal : intermediateBasis.index)
    (hintermediatePrincipal : (intermediateBasis.representation intermediatePrincipal).character = 1)
    (label : intermediateBasis.index)
    (himage : brauerNormalizerCharacterResidueHom ideal prime primary hprimary intermediate hcontains hnormalizes
      intermediateBasis label = centralCharacterResidueHom basis ideal principal) :
    centralCharacterResidueHom intermediateBasis ideal label =
      centralCharacterResidueHom intermediateBasis ideal intermediatePrincipal := by
  let counterexample : Subgroup group → Prop := fun selected =>
    ∃ (selectedGroup : IsPGroup prime selected) (selectedIntermediate : Subgroup group)
      (selectedContains : selected ≤ selectedIntermediate)
      (selectedCentralizer : Subgroup.centralizer (selected : Set group) ≤ selectedIntermediate)
      (selectedNormalizer : selectedIntermediate ≤ Subgroup.normalizer (selected : Set group))
      (selectedBasis : FiniteIrreducibleCharacterBasis selectedIntermediate)
      (selectedPrincipal selectedLabel : selectedBasis.index),
      (selectedBasis.representation selectedPrincipal).character = 1 ∧
      brauerNormalizerCharacterResidueHom ideal prime selected selectedGroup selectedIntermediate selectedCentralizer
        selectedNormalizer selectedBasis selectedLabel = centralCharacterResidueHom basis ideal principal ∧
      centralCharacterResidueHom selectedBasis ideal selectedLabel ≠
        centralCharacterResidueHom selectedBasis ideal selectedPrincipal
  by_contra hnonprincipal
  have hnonempty : Nonempty {selected : Subgroup group // counterexample selected} :=
    ⟨⟨primary, hprimary, intermediate, hprimaryContains, hcontains, hnormalizes, intermediateBasis,
      intermediatePrincipal, label, hintermediatePrincipal, himage, hnonprincipal⟩⟩
  let : Nonempty {selected : Subgroup group // counterexample selected} := hnonempty
  obtain ⟨selected, hmaximal⟩ := Finite.exists_max
    (fun selected : {selected : Subgroup group // counterexample selected} => Nat.card selected.val)
  obtain ⟨selectedGroup, selectedIntermediate, selectedContains, selectedCentralizer, selectedNormalizer,
    selectedBasis, selectedPrincipal, selectedLabel, hselectedPrincipal, hselectedImage, hselectedNonprincipal⟩ :=
      selected.property
  obtain ⟨normalizerBasis, normalizerPrincipal, normalizerLabel, hnormalizerPrincipal,
    hnormalizerImage, hnormalizerNonprincipal⟩ :=
      brauerNormalizer_principal_preimage_normalizer_replacement basis ideal prime selected.val selectedGroup
        selectedIntermediate selectedContains selectedCentralizer selectedNormalizer selectedBasis principal hprincipal
          selectedPrincipal hselectedPrincipal selectedLabel hselectedImage hselectedNonprincipal
  obtain ⟨larger, smaller, largerGroup, largerContains, largerCentralizer, largerNormalizer,
    smallerBasis, smallerPrincipal, smallerLabel, hstrict, hsmallerPrincipal, hsmallerImage, hsmallerNonprincipal⟩ :=
      normalizer_principal_preimage_strict_growth basis ideal prime selected.val selectedGroup normalizerBasis
        principal hprincipal normalizerPrincipal normalizerLabel hnormalizerPrincipal hnormalizerImage hnormalizerNonprincipal
  have hcounterexample : counterexample larger :=
    ⟨largerGroup, smaller, largerContains, largerCentralizer, largerNormalizer, smallerBasis,
      smallerPrincipal, smallerLabel, hsmallerPrincipal, hsmallerImage, hsmallerNonprincipal⟩
  exact (Nat.not_lt_of_ge (hmaximal ⟨larger, hcounterexample⟩)) hstrict

theorem brauerNormalizer_principal_residue_iff {group : Type*} [Group group] [Fintype group]
    (basis : FiniteIrreducibleCharacterBasis group)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    (prime : ℕ) [Fact prime.Prime] [CharP (ComplexAlgebraicIntegers ⧸ ideal) prime]
    (primary : Subgroup group) (hprimary : IsPGroup prime primary) (intermediate : Subgroup group)
    (hprimaryContains : primary ≤ intermediate)
    (hcontains : Subgroup.centralizer (primary : Set group) ≤ intermediate)
    (hnormalizes : intermediate ≤ Subgroup.normalizer (primary : Set group))
    (intermediateBasis : FiniteIrreducibleCharacterBasis intermediate)
    (principal : basis.index) (hprincipal : (basis.representation principal).character = 1)
    (intermediatePrincipal : intermediateBasis.index)
    (hintermediatePrincipal : (intermediateBasis.representation intermediatePrincipal).character = 1)
    (label : intermediateBasis.index) :
    brauerNormalizerCharacterResidueHom ideal prime primary hprimary intermediate hcontains hnormalizes
        intermediateBasis label = centralCharacterResidueHom basis ideal principal ↔
      centralCharacterResidueHom intermediateBasis ideal label =
        centralCharacterResidueHom intermediateBasis ideal intermediatePrincipal := by
  constructor
  · exact brauerNormalizer_principal_residue_preimage basis ideal prime primary hprimary intermediate
      hprimaryContains hcontains hnormalizes intermediateBasis principal hprincipal intermediatePrincipal hintermediatePrincipal label
  · intro hequal
    apply RingHom.ext
    intro value
    have himage := congrArg (fun hom => hom value) (brauerNormalizer_principal_residue_image basis ideal prime
      primary hprimary intermediate hcontains hnormalizes intermediateBasis principal hprincipal
        intermediatePrincipal hintermediatePrincipal)
    change centralCharacterResidueHom intermediateBasis ideal label
      (centralNormalizerCoefficientProjection _ primary intermediate hcontains hnormalizes value) = _
    rw [hequal]
    exact himage

theorem brauerNormalizer_principal_block_iff {group : Type*} [Group group] [Fintype group]
    (basis : FiniteIrreducibleCharacterBasis group)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    (prime : ℕ) [Fact prime.Prime] [CharP (ComplexAlgebraicIntegers ⧸ ideal) prime]
    (primary : Subgroup group) (hprimary : IsPGroup prime primary) (intermediate : Subgroup group)
    (hprimaryContains : primary ≤ intermediate)
    (hcontains : Subgroup.centralizer (primary : Set group) ≤ intermediate)
    (hnormalizes : intermediate ≤ Subgroup.normalizer (primary : Set group))
    (intermediateBasis : FiniteIrreducibleCharacterBasis intermediate)
    (principal : basis.index) (hprincipal : (basis.representation principal).character = 1)
    (intermediatePrincipal : intermediateBasis.index)
    (hintermediatePrincipal : (intermediateBasis.representation intermediatePrincipal).character = 1)
    (localLabel : intermediateBasis.index) (ambientLabel : basis.index)
    (himage : brauerNormalizerCharacterResidueHom ideal prime primary hprimary intermediate hcontains hnormalizes
      intermediateBasis localLabel = centralCharacterResidueHom basis ideal ambientLabel) :
    sameCoefficientBlock basis (localizedComplexIntegerRing ideal) ambientLabel principal ↔
      sameCoefficientBlock intermediateBasis (localizedComplexIntegerRing ideal) localLabel intermediatePrincipal := by
  rw [sameCoefficientBlock_iff_centralCharacterResidueHom_eq,
    sameCoefficientBlock_iff_centralCharacterResidueHom_eq, ← himage]
  exact brauerNormalizer_principal_residue_iff basis ideal prime primary hprimary intermediate hprimaryContains
    hcontains hnormalizes intermediateBasis principal hprincipal intermediatePrincipal hintermediatePrincipal localLabel

end CFSG.TwoRankLowerBound.Helpers
