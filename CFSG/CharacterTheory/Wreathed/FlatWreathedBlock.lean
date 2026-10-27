module

public import CFSG.CharacterTheory.Wreathed.FullDefectBlockLabels
public import CFSG.CharacterTheory.Wreathed.CompatibleCentralizerFamilies

public section

open scoped BigOperators Classical

namespace CFSG.Wreathed

open CFSG.TwoRankLowerBound.Helpers CFSG.Wreathed.FullDefectLabels

variable {G : Type*} [Group G] [Fintype G]

@[expose] def FlatWreathedBlock (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] {n : ℕ} (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) (B : basis.index) : Prop :=
  coefficientBlockDefect basis ideal 2 B S ∧
  ∃ (eb : FiniteIrreducibleCharacterBasis (BaseFourCentralizerStructure.ambientOddCore
      (Subgroup.centralizer ((S : Subgroup G) : Set G)))) (θ : eb.index)
    (nb : FiniteIrreducibleCharacterBasis (Subgroup.normalizer ((S : Subgroup G) : Set G)))
    (θhat : nb.index),
    InflatedLabel (oddCore_le_normalizer S) nb eb θ θhat ∧
    brauerNormalizerCharacterResidueHom ideal 2 (S : Subgroup G) S.isPGroup'
        (Subgroup.normalizer ((S : Subgroup G) : Set G)) (Subgroup.centralizer_le_normalizer _)
        le_rfl nb θhat =
      centralCharacterResidueHom basis ideal B ∧
    ∃ θt : Subgroup.centralizer ((S : Subgroup G) : Set G) → ℂ,
      (∀ (c : Subgroup.centralizer ((S : Subgroup G) : Set G)) (z : G)
        (y : BaseFourCentralizerStructure.ambientOddCore
          (Subgroup.centralizer ((S : Subgroup G) : Set G))),
        z ∈ Subgroup.zpowers (wreathModelHom S e (Original.a (2 ^ n))) → (c : G) = z * y →
          θt c = (eb.representation θ).character y) ∧
      ∃ ψ, CompatibleCentralizerFamily 2 (S : Subgroup G) θt ψ

theorem centralCharacterResidueHom_eq_of_character_eq {K : Type*} [Group K] [Fintype K]
    (basis₁ basis₂ : FiniteIrreducibleCharacterBasis K) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] {label₁ : basis₁.index} {label₂ : basis₂.index}
    (h : (basis₁.representation label₁).character = (basis₂.representation label₂).character) :
    centralCharacterResidueHom basis₁ ideal label₁ =
      centralCharacterResidueHom basis₂ ideal label₂ := by
  apply RingHom.ext
  intro w
  change localizedComplexIntegerResidue ideal (localCentralCharacterHom basis₁ ideal label₁ w) =
    localizedComplexIntegerResidue ideal (localCentralCharacterHom basis₂ ideal label₂ w)
  congr 1
  apply Subtype.ext
  rw [localCentralCharacterHom_coe, localCentralCharacterHom_coe]
  unfold centralCharacterScalar
  rw [h]

theorem brauerNormalizerCharacterResidueHom_eq_of_character_eq
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal] (p : ℕ) [Fact p.Prime]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) p] (Q : Subgroup G) (hQ : IsPGroup p Q)
    (H : Subgroup G) (hCH : Subgroup.centralizer (Q : Set G) ≤ H)
    (hHN : H ≤ Subgroup.normalizer (Q : Set G)) (basis₁ basis₂ : FiniteIrreducibleCharacterBasis H)
    {label₁ : basis₁.index} {label₂ : basis₂.index}
    (h : (basis₁.representation label₁).character = (basis₂.representation label₂).character) :
    brauerNormalizerCharacterResidueHom ideal p Q hQ H hCH hHN basis₁ label₁ =
      brauerNormalizerCharacterResidueHom ideal p Q hQ H hCH hHN basis₂ label₂ := by
  apply RingHom.ext
  intro z
  change centralCharacterResidueHom basis₁ ideal label₁ _ =
    centralCharacterResidueHom basis₂ ideal label₂ _
  rw [centralCharacterResidueHom_eq_of_character_eq basis₁ basis₂ ideal h]

theorem canonicalLabel_character_eq (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] {n : ℕ} (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) {B : basis.index}
    (eb : FiniteIrreducibleCharacterBasis (BaseFourCentralizerStructure.ambientOddCore
      (Subgroup.centralizer ((S : Subgroup G) : Set G)))) (θ : eb.index)
    (nb : FiniteIrreducibleCharacterBasis (Subgroup.normalizer ((S : Subgroup G) : Set G)))
    (θhat : nb.index) (hθ : InflatedLabel (oddCore_le_normalizer S) nb eb θ θhat)
    (hB : brauerNormalizerCharacterResidueHom ideal 2 (S : Subgroup G) S.isPGroup'
        (Subgroup.normalizer ((S : Subgroup G) : Set G)) (Subgroup.centralizer_le_normalizer _)
        le_rfl nb θhat = centralCharacterResidueHom basis ideal B)
    (eb' : FiniteIrreducibleCharacterBasis (BaseFourCentralizerStructure.ambientOddCore
      (Subgroup.centralizer ((S : Subgroup G) : Set G)))) (θ' : eb'.index)
    (nb' : FiniteIrreducibleCharacterBasis (Subgroup.normalizer ((S : Subgroup G) : Set G)))
    (θhat' : nb'.index) (hθ' : InflatedLabel (oddCore_le_normalizer S) nb' eb' θ' θhat')
    (hB' : brauerNormalizerCharacterResidueHom ideal 2 (S : Subgroup G) S.isPGroup'
        (Subgroup.normalizer ((S : Subgroup G) : Set G)) (Subgroup.centralizer_le_normalizer _)
        le_rfl nb' θhat' = centralCharacterResidueHom basis ideal B) :
    (eb.representation θ).character = (eb'.representation θ').character := by
  obtain ⟨θ₀, hθ₀⟩ := finiteIrreducibleCharacterBasis_contains_irreducible eb
    (eb'.representation θ') (eb'.irreducible θ')
  obtain ⟨θhat₀, hθhat₀⟩ := finiteIrreducibleCharacterBasis_contains_irreducible nb
    (nb'.representation θhat') (nb'.irreducible θhat')
  have hinf₀ : InflatedLabel (oddCore_le_normalizer S) nb eb θ₀ θhat₀ := by
    intro v x
    rw [hθhat₀, hθ₀]
    exact hθ' v x
  have hB₀ : brauerNormalizerCharacterResidueHom ideal 2 (S : Subgroup G) S.isPGroup'
      (Subgroup.normalizer ((S : Subgroup G) : Set G)) (Subgroup.centralizer_le_normalizer _)
      le_rfl nb θhat₀ = centralCharacterResidueHom basis ideal B := by
    rw [brauerNormalizerCharacterResidueHom_eq_of_character_eq ideal 2 _ _ _ _ _ nb nb' hθhat₀]
    exact hB'
  obtain ⟨principal, hprincipal⟩ := finiteIrreducibleCharacterBasis_contains_irreducible basis
    (principalFiniteComplexRepresentation G) (principalFiniteComplexRepresentation_isIrreducible G)
  rw [principalFiniteComplexRepresentation_character] at hprincipal
  have hlabels := full_defect_block_canonical_sylow_centralizer_labels basis ideal n hn S e nb eb
    principal hprincipal
  have heq : θ = θ₀ := hlabels.2.2.2.2.2.2.2.1 θ θ₀ θhat θhat₀ hθ hinf₀ (hB.trans hB₀.symm)
  rw [heq, hθ₀]

theorem FlatWreathedBlock.exists_family {basis : FiniteIrreducibleCharacterBasis G}
    {ideal : Ideal ComplexAlgebraicIntegers} [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] {n : ℕ} (hn : 2 ≤ n) {S : Sylow 2 G}
    {e : S ≃* Wreath (2 ^ n)} {B : basis.index} (hflat : FlatWreathedBlock basis ideal S e B)
    (eb : FiniteIrreducibleCharacterBasis (BaseFourCentralizerStructure.ambientOddCore
      (Subgroup.centralizer ((S : Subgroup G) : Set G)))) (θ : eb.index)
    (nb : FiniteIrreducibleCharacterBasis (Subgroup.normalizer ((S : Subgroup G) : Set G)))
    (θhat : nb.index) (hθ : InflatedLabel (oddCore_le_normalizer S) nb eb θ θhat)
    (hB : brauerNormalizerCharacterResidueHom ideal 2 (S : Subgroup G) S.isPGroup'
        (Subgroup.normalizer ((S : Subgroup G) : Set G)) (Subgroup.centralizer_le_normalizer _)
        le_rfl nb θhat = centralCharacterResidueHom basis ideal B)
    (θt : Subgroup.centralizer ((S : Subgroup G) : Set G) → ℂ)
    (hθt : ∀ (c : Subgroup.centralizer ((S : Subgroup G) : Set G)) (z : G)
      (y : BaseFourCentralizerStructure.ambientOddCore
        (Subgroup.centralizer ((S : Subgroup G) : Set G))),
      z ∈ Subgroup.zpowers (wreathModelHom S e (Original.a (2 ^ n))) → (c : G) = z * y →
        θt c = (eb.representation θ).character y) :
    ∃ ψ, CompatibleCentralizerFamily 2 (S : Subgroup G) θt ψ := by
  obtain ⟨-, eb', θ', nb', θhat', hθ', hB', θt', hθt', ψ, hψ⟩ := hflat
  have hchar := canonicalLabel_character_eq basis ideal hn S e eb θ nb θhat hθ hB eb' θ' nb'
    θhat' hθ' hB'
  have heq : θt' = θt := by
    funext c
    obtain ⟨z, hz, y, hzy⟩ := CompatibleFamilies.exists_center_mul_oddCore S e hn c
    rw [BrauerWong.modelCenter_eq_zpowers S e] at hz
    rw [hθt c z y hz hzy, hθt' c z y hz hzy, hchar]
  exact ⟨ψ, heq ▸ hψ⟩

theorem FlatWreathedBlock.of_family (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] {n : ℕ} (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) {B : basis.index}
    (eb : FiniteIrreducibleCharacterBasis (BaseFourCentralizerStructure.ambientOddCore
      (Subgroup.centralizer ((S : Subgroup G) : Set G)))) (θ : eb.index)
    (nb : FiniteIrreducibleCharacterBasis (Subgroup.normalizer ((S : Subgroup G) : Set G)))
    (θhat : nb.index) (hθ : InflatedLabel (oddCore_le_normalizer S) nb eb θ θhat)
    (hB : brauerNormalizerCharacterResidueHom ideal 2 (S : Subgroup G) S.isPGroup'
        (Subgroup.normalizer ((S : Subgroup G) : Set G)) (Subgroup.centralizer_le_normalizer _)
        le_rfl nb θhat = centralCharacterResidueHom basis ideal B)
    (θt : Subgroup.centralizer ((S : Subgroup G) : Set G) → ℂ)
    (hθt : ∀ (c : Subgroup.centralizer ((S : Subgroup G) : Set G)) (z : G)
      (y : BaseFourCentralizerStructure.ambientOddCore
        (Subgroup.centralizer ((S : Subgroup G) : Set G))),
      z ∈ Subgroup.zpowers (wreathModelHom S e (Original.a (2 ^ n))) → (c : G) = z * y →
        θt c = (eb.representation θ).character y)
    {ψ : ∀ Q : Subgroup G, Subgroup.centralizer (Q : Set G) →* ℂˣ}
    (hψ : CompatibleCentralizerFamily 2 (S : Subgroup G) θt ψ) :
    FlatWreathedBlock basis ideal S e B := by
  refine ⟨?_, eb, θ, nb, θhat, hθ, hB, θt, hθt, ψ, hψ⟩
  obtain ⟨principal, hprincipal⟩ := finiteIrreducibleCharacterBasis_contains_irreducible basis
    (principalFiniteComplexRepresentation G) (principalFiniteComplexRepresentation_isIrreducible G)
  rw [principalFiniteComplexRepresentation_character] at hprincipal
  obtain ⟨B', hB', hdefect⟩ := (full_defect_block_canonical_sylow_centralizer_labels basis ideal n
    hn S e nb eb principal hprincipal).2.2.2.2.2.1 θ θhat hθ
  have hres : centralCharacterResidueHom basis ideal B =
      centralCharacterResidueHom basis ideal B' := hB.symm.trans hB'
  unfold coefficientBlockDefect at hdefect ⊢
  rw [hres]
  exact hdefect

theorem FlatWreathedBlock.defect {basis : FiniteIrreducibleCharacterBasis G}
    {ideal : Ideal ComplexAlgebraicIntegers} [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] {n : ℕ} {S : Sylow 2 G}
    {e : S ≃* Wreath (2 ^ n)} {B : basis.index} (hflat : FlatWreathedBlock basis ideal S e B) :
    coefficientBlockDefect basis ideal 2 B S :=
  hflat.1

end CFSG.Wreathed
