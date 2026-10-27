module

public import CFSG.CharacterTheory.Wreathed.FlatBlockCountLabels
public import CFSG.CharacterTheory.Wreathed.CompatibleBoundaryCount

public section

open scoped BigOperators Classical

namespace CFSG.Wreathed

open CFSG.TwoRankLowerBound.Helpers CFSG.Wreathed.FullDefectLabels
  CFSG.Wreathed.BaseFourCentralizerStructure CFSG.Wreathed.CompatibleFamilies

variable {G : Type*} [Group G] [Fintype G]

theorem card_flatWreathedBlocks [IsSimpleGroup G] (hnonab : ∃ x y : G, x * y ≠ y * x)
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) (η : G)
    (hη : η ∈ Subgroup.normalizer ((Subgroup.closure {wreathModelHom S e (Original.s (2 ^ n)),
      wreathModelHom S e (Original.t (2 ^ n))} : Subgroup G) : Set G))
    (hord : orderOf ((Subgroup.closure {wreathModelHom S e (Original.s (2 ^ n)),
      wreathModelHom S e (Original.t (2 ^ n))}).normalizerMonoidHom ⟨η, hη⟩) = 3) :
    (flatWreathedBlocks basis ideal S e).card = (boundaryKernel S e η).index := by
  obtain ⟨eb⟩ := finiteIrreducibleCharacterBasis_exists
    (G := ambientOddCore (Subgroup.centralizer ((S : Subgroup G) : Set G)))
  obtain ⟨nb⟩ := finiteIrreducibleCharacterBasis_exists
    (G := Subgroup.normalizer ((S : Subgroup G) : Set G))
  obtain ⟨qb⟩ := finiteIrreducibleCharacterBasis_exists
    (G := ambientOddCore (Subgroup.centralizer ((S : Subgroup G) : Set G)) ⧸ boundaryKernel S e η)
  obtain ⟨-, -, -, -, -, hK, -, -, -, -, hcount⟩ :=
    compatible_centralizer_boundary_character_count hnonab n hn S e eb η hη hord qb
  obtain ⟨g, -⟩ := exists_equiv_flatWreathedBlocks basis ideal hn S e eb nb _ rfl
  rw [← Nat.card_eq_finsetCard, ← Nat.card_congr g, Nat.card_coe_set_eq, hK]
  exact hcount

theorem flat_block_count_corrected_three_cycle_commutator [IsSimpleGroup G]
    (hnonab : ∃ x y : G, x * y ≠ y * x) (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n))
    (eb : FiniteIrreducibleCharacterBasis
      (ambientOddCore (Subgroup.centralizer ((S : Subgroup G) : Set G))))
    (nb : FiniteIrreducibleCharacterBasis (Subgroup.normalizer ((S : Subgroup G) : Set G))) :
    let s := wreathModelHom S e (Original.s (2 ^ n))
    let t := wreathModelHom S e (Original.t (2 ^ n))
    let U := Subgroup.closure {s, t}
    let x := (s * t) ^ (2 ^ n / 2)
    let T := Subgroup.closure {s ^ (2 ^ n / 2), t ^ (2 ^ n / 2)}
    let N := Subgroup.centralizer {x}
    let C₀ := ambientOddCore (Subgroup.centralizer (T : Set G))
    let E := ambientOddCore (Subgroup.centralizer ((S : Subgroup G) : Set G))
    let N' := (commutator N).map N.subtype
    ∀ (η : G) (hη : η ∈ Subgroup.normalizer (U : Set G)),
      orderOf (U.normalizerMonoidHom ⟨η, hη⟩) = 3 →
      ∀ qb : FiniteIrreducibleCharacterBasis (E ⧸ boundaryKernel S e η),
      let J := E ⊓ (Subgroup.closure {y : G | ∃ c ∈ C₀, y = c⁻¹ * (η⁻¹ * c * η)} ⊔ N')
      boundaryKernel S e η = J.subgroupOf E ∧ IsMulCommutative (E ⧸ boundaryKernel S e η) ∧
      (∀ 𝔅 ∈ flatWreathedBlocks basis ideal S e, ∀ B ∈ 𝔅,
        ∃ (θ : eb.index) (θhat : nb.index), InflatedLabel (oddCore_le_normalizer S) nb eb θ θhat ∧
          brauerNormalizerCharacterResidueHom ideal 2 (S : Subgroup G) S.isPGroup'
              (Subgroup.normalizer ((S : Subgroup G) : Set G))
              (Subgroup.centralizer_le_normalizer _) le_rfl nb θhat =
            centralCharacterResidueHom basis ideal B) ∧
      (∃ f : flatWreathedBlocks basis ideal S e ≃ qb.index,
        ∀ (𝔅 : flatWreathedBlocks basis ideal S e) (B : basis.index),
          B ∈ (𝔅 : Finset basis.index) → ∀ (θ : eb.index) (θhat : nb.index),
          InflatedLabel (oddCore_le_normalizer S) nb eb θ θhat →
          brauerNormalizerCharacterResidueHom ideal 2 (S : Subgroup G) S.isPGroup'
              (Subgroup.normalizer ((S : Subgroup G) : Set G))
              (Subgroup.centralizer_le_normalizer _) le_rfl nb θhat =
            centralCharacterResidueHom basis ideal B →
          (eb.representation θ).character =
            (qb.representation (f 𝔅)).character ∘ QuotientGroup.mk) ∧
      (flatWreathedBlocks basis ideal S e).card = J.relIndex E ∧
      ∀ (ideal' : Ideal ComplexAlgebraicIntegers) [ideal'.IsMaximal]
        [CharP (ComplexAlgebraicIntegers ⧸ ideal') 2],
        (flatWreathedBlocks basis ideal' S e).card = (flatWreathedBlocks basis ideal S e).card := by
  intro s t U x T N C₀ E N' η hη hord qb J
  obtain ⟨-, -, -, -, -, hK, -, hcomm, ⟨f₀, hf₀⟩, -, hcount⟩ :=
    compatible_centralizer_boundary_character_count hnonab n hn S e eb η hη hord qb
  obtain ⟨g, hg⟩ := exists_equiv_flatWreathedBlocks basis ideal hn S e eb nb _ rfl
  refine ⟨hK, hcomm, fun 𝔅 h𝔅 B hB =>
    exists_canonicalLabel_of_mem_flatWreathedBlocks basis ideal hn S e eb nb h𝔅 hB,
    ⟨(f₀.trans g).symm, fun 𝔅 B hB θ θhat hθ hBr => ?_⟩, ?_, fun ideal' _ _ => ?_⟩
  · have h1 : g (f₀ ((f₀.trans g).symm 𝔅)) = 𝔅 := (f₀.trans g).apply_symm_apply 𝔅
    have h2 := hg (f₀ ((f₀.trans g).symm 𝔅)) B (by rw [h1]; exact hB) θ θhat hθ hBr
    rw [h2, hf₀]
  · rw [← Nat.card_eq_finsetCard, ← Nat.card_congr g, Nat.card_coe_set_eq]
    exact hcount
  · rw [card_flatWreathedBlocks hnonab basis ideal' n hn S e η hη hord,
      card_flatWreathedBlocks hnonab basis ideal n hn S e η hη hord]

end CFSG.Wreathed
