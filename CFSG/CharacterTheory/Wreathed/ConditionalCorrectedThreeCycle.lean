module

public import CFSG.CharacterTheory.Wreathed.FlatBlockCount
public import CFSG.CharacterTheory.Wreathed.ConditionalEveryFlat
public import CFSG.LocalAnalysis.RankTwoShapes.Homocyclic.ExponentTwo

public section

open scoped Classical

namespace CFSG.Wreathed.ConditionalCorrectedThreeCycle

open CFSG.Wreathed.ActualProjectiveLayer CFSG.Wreathed.BaseFourCentralizerStructure
  CFSG.TwoRankLowerBound.Helpers CFSG.Wreathed.LinearLocalTwistMoment

theorem card_flatWreathedBlocks_eq_one
    {G : Type} [Group G] [Fintype G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : p ≠ 2) (hf : 1 ≤ f)
    (hmodel : PSLTwoClassicalModel (centralizerSimpleLayer n hn S e) p f)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (basis : FiniteIrreducibleCharacterBasis G)
    (η : G) (hη : η ∈ Subgroup.normalizer (modelBase S e : Set G))
    (hord : orderOf ((modelBase S e).normalizerMonoidHom ⟨η, hη⟩) = 3) :
    (flatWreathedBlocks basis ideal S e).card = 1 := by
  obtain ⟨-, -, -, -, -, -, -, hpflat⟩ := FlatEvery.principal_flat basis ideal hn S e
  rw [Finset.card_eq_one]
  refine ⟨coefficientBlock basis (localizedComplexIntegerRing ideal)
    (principalCharacterLabel basis), ?_⟩
  ext 𝔅
  rw [Finset.mem_singleton]
  constructor
  · intro h𝔅
    obtain ⟨B, hBflat, rfl⟩ := mem_flatWreathedBlocks.mp h𝔅
    obtain ⟨eb⟩ := finiteIrreducibleCharacterBasis_exists
      (G := ambientOddCore (Subgroup.centralizer ((S : Subgroup G) : Set G)))
    obtain ⟨nb⟩ := finiteIrreducibleCharacterBasis_exists
      (G := Subgroup.normalizer ((S : Subgroup G) : Set G))
    obtain ⟨θ, θhat, hθ, hB⟩ := exists_canonicalLabel_of_mem_flatWreathedBlocks basis ideal hn S e
      eb nb h𝔅 (coefficientBlock_self_mem basis _ B)
    exact ((conditional_every_flat_block_has_one_linear_character hnonab n hn S e hfour p f hp
      hpodd hf hmodel ideal basis B hBflat eb θ nb θhat hθ hB η hη hord).2.2.2.1
        (principalCharacterLabel basis) (principalCharacterLabel_character basis)).1
  · rintro rfl
    exact mem_flatWreathedBlocks.mpr ⟨_, hpflat, rfl⟩

theorem conditional_corrected_three_cycle_commutator_index_one
    {G : Type} [Group G]
    [Fintype G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a) (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : p ≠ 2) (hf : 1 ≤ f)
    (hmodel : PSLTwoClassicalModel (centralizerSimpleLayer n hn S e) p f) (η : G)
    (hη : η ∈ Subgroup.normalizer ((Subgroup.closure {wreathModelHom S e (Original.s (2 ^ n)),
      wreathModelHom S e (Original.t (2 ^ n))} : Subgroup G) : Set G))
    (hord : orderOf ((Subgroup.closure {wreathModelHom S e (Original.s (2 ^ n)),
      wreathModelHom S e (Original.t (2 ^ n))}).normalizerMonoidHom ⟨η, hη⟩) = 3) :
    (CompatibleFamilies.boundaryKernel S e η).index = 1 ∧
      ambientOddCore (Subgroup.centralizer ((S : Subgroup G) : Set G)) ≤
        CompatibleFamilies.boundaryProduct S e η := by
  obtain ⟨ideal, hmax, hchar⟩ := CFSG.RankTwoShapes.exists_maximal_ideal_residue_two
  obtain ⟨basis⟩ := finiteIrreducibleCharacterBasis_exists (G := G)
  have hcard := card_flatWreathedBlocks hnonab basis ideal n hn S e η hη hord
  have hU := modelBase_eq_actual_generated S e (m := 2 ^ n)
  revert hη hord
  rw [← hU]
  intro hη hord
  rw [card_flatWreathedBlocks_eq_one hnonab n hn S e hfour p f hp hpodd hf hmodel ideal basis η
    hη hord] at hcard
  refine ⟨hcard.symm, fun c hc => ?_⟩
  have htop := Subgroup.index_eq_one.mp hcard.symm
  have hmem : (⟨c, hc⟩ : ambientOddCore (Subgroup.centralizer ((S : Subgroup G) : Set G))) ∈
      CompatibleFamilies.boundaryKernel S e η := htop ▸ Subgroup.mem_top _
  exact (Subgroup.mem_subgroupOf.mp hmem).2

end CFSG.Wreathed.ConditionalCorrectedThreeCycle
