module

public import CFSG.LocalAnalysis.LargeEvenClassification.AbelianNormalRank
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallAbelianModels
public import CFSG.LocalAnalysis.LargeEvenClassification.NormalFourGenerators
public import CFSG.LocalAnalysis.LargeEvenClassification.AbelianCoordinates

public section

open CFSG.Open

namespace CFSG.LargeEvenClassification.Helpers

universe groupUniverse

theorem exists_maximal_abelian_normal {Ambient : Type groupUniverse} [Group Ambient]
    [Finite Ambient] : ∃ Normal : Subgroup Ambient, Normal.Normal ∧ IsMulCommutative Normal ∧
      ∀ Larger : Subgroup Ambient,
        Larger.Normal → IsMulCommutative Larger → Normal ≤ Larger → Larger ≤ Normal := by
  have hbottom : (⊥ : Subgroup Ambient).Normal ∧ IsMulCommutative (⊥ : Subgroup Ambient) :=
    ⟨inferInstance, inferInstance⟩
  obtain ⟨Normal, _, hmaximal⟩ := Finite.exists_le_maximal
    (p := fun Normal : Subgroup Ambient => Normal.Normal ∧ IsMulCommutative Normal) hbottom
  refine ⟨Normal, hmaximal.1.1, hmaximal.1.2, ?_⟩
  intro Larger hnormal hcommutative hle
  exact hmaximal.2 ⟨hnormal, hcommutative⟩ hle

theorem small_rank_two_selfCentralizing_four_generators {Ambient : Type groupUniverse}
    [Group Ambient] [Finite Ambient] (hpgroup : IsPGroup 2 Ambient)
    (Normal : Subgroup Ambient) [Normal.Normal] {upper lower : ℕ}
    (hlower : 0 < lower) (hordered : lower ≤ upper) (hsmall : upper + lower ≤ 3)
    (coordinates : Normal ≃* Multiplicative (ZMod (2 ^ upper)) ×
      Multiplicative (ZMod (2 ^ lower)))
    (hselfCentralizing : Subgroup.centralizer (Normal : Set Ambient) = Normal)
    (SubgroupOfAmbient : Subgroup Ambient) :
    ∃ generators : Finset SubgroupOfAmbient,
      Subgroup.closure (generators : Set SubgroupOfAmbient) = ⊤ ∧ generators.card ≤ 4 := by
  have hcases : (upper = 1 ∧ lower = 1) ∨ (upper = 2 ∧ lower = 1) := by omega
  rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have hcommutative : IsMulCommutative Normal := by
      apply isMulCommutative_iff.mpr
      intro first second
      apply coordinates.injective
      rw [map_mul, map_mul, mul_comm]
    have hcard : Nat.card Normal = 4 := by
      rw [Nat.card_congr coordinates.toEquiv, Nat.card_eq_fintype_card]
      decide
    obtain ⟨generators, hgenerates, hcardBound⟩ := abelian_normal_four_three_generators hpgroup Normal
      hcommutative hcard hselfCentralizing SubgroupOfAmbient
    exact ⟨generators, hgenerates, hcardBound.trans (by decide)⟩
  · exact fourTwo_selfCentralizing_four_generators hpgroup Normal coordinates
      hselfCentralizing SubgroupOfAmbient

theorem no_normal_eight_large_generator_rank_coordinates {Ambient : Type groupUniverse}
    [Group Ambient] [Finite Ambient] (hpgroup : IsPGroup 2 Ambient)
    (hnoEight : ∀ Elementary : Subgroup Ambient, Elementary.Normal →
      IsElemAbelian 2 Elementary → Nat.card Elementary ≠ 8)
    (hlarge : 5 ≤ pGeneratorRank 2 Ambient) :
    ∃ (Normal : Subgroup Ambient) (upper lower : ℕ), Normal.Normal ∧ IsMulCommutative Normal ∧
      Subgroup.centralizer (Normal : Set Ambient) = Normal ∧ 0 < lower ∧ lower ≤ upper ∧
      4 ≤ upper + lower ∧
      Nonempty (Normal ≃* Multiplicative (ZMod (2 ^ upper)) ×
        Multiplicative (ZMod (2 ^ lower))) := by
  obtain ⟨Normal, hnormal, hcommutative, hmaximal⟩ := exists_maximal_abelian_normal (Ambient := Ambient)
  let := hnormal
  let : CommGroup Normal := { (inferInstance : Group Normal) with
    mul_comm := @mul_comm' Normal _ hcommutative }
  have hselfCentralizing := maximal_abelian_normal_selfCentralizing Nat.prime_two hpgroup
    Normal hcommutative hmaximal
  obtain ⟨normalGenerators, hnormalGenerates, hnormalCard⟩ :=
    no_normal_eight_abelian_normal_two_generators hpgroup hnoEight Normal hcommutative
  have hnormalRank := (pGeneratorRank_le_generators Nat.prime_two
    (hpgroup.to_subgroup Normal) normalGenerators hnormalGenerates).trans hnormalCard
  have hrankTop : pGeneratorRank 2 (⊤ : Subgroup Ambient) = pGeneratorRank 2 Ambient :=
    pGeneratorRank_mulEquiv Nat.prime_two (hpgroup.to_subgroup ⊤) Subgroup.topEquiv
  rcases commutative_pGroup_rank_two_coordinates Nat.prime_two (hpgroup.to_subgroup Normal)
      hnormalRank with hcyclic | ⟨upper, lower, hlower, hordered, ⟨coordinates⟩⟩
  · let := hcyclic
    obtain ⟨generators, hgenerates, hcard⟩ := cyclic_maximal_abelian_normal_three_generators
      hpgroup Normal hmaximal ⊤
    have hbound := (pGeneratorRank_le_generators Nat.prime_two (hpgroup.to_subgroup ⊤)
      generators hgenerates).trans hcard
    rw [hrankTop] at hbound
    omega
  · have hlargeExponents : 4 ≤ upper + lower := by
      by_contra hsmall
      obtain ⟨generators, hgenerates, hcard⟩ := small_rank_two_selfCentralizing_four_generators
        hpgroup Normal hlower hordered (by omega) coordinates hselfCentralizing ⊤
      have hbound := (pGeneratorRank_le_generators Nat.prime_two (hpgroup.to_subgroup ⊤)
        generators hgenerates).trans hcard
      rw [hrankTop] at hbound
      omega
    exact ⟨Normal, upper, lower, hnormal, hcommutative, hselfCentralizing,
      hlower, hordered, hlargeExponents, ⟨coordinates⟩⟩

theorem large_even_local_core_pGeneratorRank (Ambient : Type groupUniverse) [Group Ambient]
    [Finite Ambient] [IsSimpleGroup Ambient]
    (hnonab : ∃ first second : Ambient, first * second ≠ second * first)
    (hK : IsKProperByOrder Ambient) (hchar : IsCharTwoType Ambient) (hrank : 4 ≤ evenRank Ambient) :
    ∃ (prime : ℕ) (Local Elementary : Subgroup Ambient),
      prime ∈ oddLocalPrimes 4 Ambient ∧ IsTwoLocal Local ∧ Local ≠ ⊤ ∧ IsKProperByOrder Local ∧
      Elementary ≤ Local ∧ IsElemAbelian prime Elementary ∧
      Nat.card Elementary = prime ^ evenRank Ambient ∧ pCoreOf 2 Local ≠ ⊥ ∧
      2 * evenRank Ambient ≤ pGeneratorRank 2 (CFSG.Open.pCore 2 Local) := by
  obtain ⟨prime, Local, Elementary, hprime, hlocal, hproper, hlocalK, hle, helementary,
    hcard, hcore, hgenerators⟩ :=
    large_even_local_core_generator_bound Ambient hnonab hK hchar hrank
  obtain ⟨generators, hgenerates, hgeneratorCard⟩ :=
    pGeneratorRank_generators Nat.prime_two (pCore_isPGroup Local 2)
  refine ⟨prime, Local, Elementary, hprime, hlocal, hproper, hlocalK, hle, helementary,
    hcard, hcore, ?_⟩
  exact hgeneratorCard ▸ hgenerators generators hgenerates

theorem large_even_core_rank_two_alternative (Ambient : Type groupUniverse) [Group Ambient]
    [Finite Ambient] [IsSimpleGroup Ambient]
    (hnonab : ∃ first second : Ambient, first * second ≠ second * first)
    (hK : IsKProperByOrder Ambient) (hchar : IsCharTwoType Ambient) (hrank : 4 ≤ evenRank Ambient) :
    ∃ (prime : ℕ) (Local Elementary : Subgroup Ambient),
      prime ∈ oddLocalPrimes 4 Ambient ∧ IsTwoLocal Local ∧ Local ≠ ⊤ ∧ IsKProperByOrder Local ∧
      Elementary ≤ Local ∧ IsElemAbelian prime Elementary ∧
      Nat.card Elementary = prime ^ evenRank Ambient ∧ pCoreOf 2 Local ≠ ⊥ ∧
      2 * evenRank Ambient ≤ pGeneratorRank 2 (CFSG.Open.pCore 2 Local) ∧
      ((∃ Eight : Subgroup (CFSG.Open.pCore 2 Local),
        Eight.Normal ∧ IsElemAbelian 2 Eight ∧ Nat.card Eight = 8) ∨
      ∃ (Normal : Subgroup (CFSG.Open.pCore 2 Local)) (upper lower : ℕ),
        Normal.Normal ∧ IsMulCommutative Normal ∧
        Subgroup.centralizer (Normal : Set (CFSG.Open.pCore 2 Local)) = Normal ∧
        0 < lower ∧ lower ≤ upper ∧ 4 ≤ upper + lower ∧
        Nonempty (Normal ≃* Multiplicative (ZMod (2 ^ upper)) ×
          Multiplicative (ZMod (2 ^ lower)))) := by
  obtain ⟨prime, Local, Elementary, hprime, hlocal, hproper, hlocalK, hle, helementary,
    hcard, hcore, hgeneratorRank⟩ :=
    large_even_local_core_pGeneratorRank Ambient hnonab hK hchar hrank
  refine ⟨prime, Local, Elementary, hprime, hlocal, hproper, hlocalK, hle, helementary,
    hcard, hcore, hgeneratorRank, ?_⟩
  classical
  by_cases hexists : ∃ Eight : Subgroup (CFSG.Open.pCore 2 Local),
      Eight.Normal ∧ IsElemAbelian 2 Eight ∧ Nat.card Eight = 8
  · exact Or.inl hexists
  · right
    apply no_normal_eight_large_generator_rank_coordinates (pCore_isPGroup Local 2)
    · intro Eight hnormal helementary height
      exact hexists ⟨Eight, hnormal, helementary, height⟩
    · omega

end CFSG.LargeEvenClassification.Helpers
