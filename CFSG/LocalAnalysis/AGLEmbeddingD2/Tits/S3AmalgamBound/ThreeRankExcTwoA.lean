module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.ThreeRankExc

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.ThreeRank


open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley TauCeti
  CFSG.TauCetiBridge CFSG.TauCetiBridge.Even

set_option linter.unusedSectionVars false



theorem two_le_pRank_three_exc_f4 {S : Type} [Group S] [Finite S] (q : PrimePower)
    (hv : (LieTypeIndex.F4 q).Valid) (e : S ≃* ValidLieTypeIndex.Group ⟨.F4 q, hv⟩) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup S) := by
  obtain ⟨K, _, _, ⟨φ⟩⟩ := exists_untwisted_model chevalleyBridgesAll.f4 q hv e
  have := four_le_pRank_three_adjointQuotient_any (τ := .F4) (Or.inl rfl) (K := K)
  rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) φ] at this
  omega

theorem two_le_pRank_three_exc_e6 {S : Type} [Group S] [Finite S] (q : PrimePower)
    (hv : (LieTypeIndex.E6 q).Valid) (e : S ≃* ValidLieTypeIndex.Group ⟨.E6 q, hv⟩) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup S) := by
  obtain ⟨K, _, _, ⟨φ⟩⟩ := exists_untwisted_model chevalleyBridgesAll.e6 q hv e
  have := four_le_pRank_three_adjointQuotient_any (τ := .E6) (Or.inr (Or.inl rfl)) (K := K)
  rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) φ] at this
  omega

theorem two_le_pRank_three_exc_e7 {S : Type} [Group S] [Finite S] (q : PrimePower)
    (hv : (LieTypeIndex.E7 q).Valid) (e : S ≃* ValidLieTypeIndex.Group ⟨.E7 q, hv⟩) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup S) := by
  obtain ⟨K, _, _, ⟨φ⟩⟩ := exists_untwisted_model chevalleyBridgesAll.e7 q hv e
  have := four_le_pRank_three_adjointQuotient_any (τ := .E7) (Or.inr (Or.inr (Or.inl rfl)))
    (K := K)
  rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) φ] at this
  omega

theorem two_le_pRank_three_exc_e8 {S : Type} [Group S] [Finite S] (q : PrimePower)
    (hv : (LieTypeIndex.E8 q).Valid) (e : S ≃* ValidLieTypeIndex.Group ⟨.E8 q, hv⟩) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup S) := by
  obtain ⟨K, _, _, ⟨φ⟩⟩ := exists_untwisted_model chevalleyBridgesAll.e8 q hv e
  have := four_le_pRank_three_adjointQuotient_any (τ := .E8) (Or.inr (Or.inr (Or.inr rfl)))
    (K := K)
  rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) φ] at this
  omega

theorem two_le_pRank_three_exc_g2 {S : Type} [Group S] [Finite S] (q : PrimePower)
    (hv : (LieTypeIndex.G2 q).Valid) (e : S ≃* ValidLieTypeIndex.Group ⟨.G2 q, hv⟩) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup S) := by
  obtain ⟨K, _, _, ⟨φ⟩⟩ := exists_untwisted_model chevalleyBridgesAll.g2 q hv e
  have := two_le_pRank_three_adjointQuotient_G2 (K := K)
  rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) φ] at this
  omega

theorem two_le_pRank_three_exc_twistedE6 {S : Type} [Group S] [Finite S] (q : PrimePower)
    (hv : (LieTypeIndex.twistedE6 q).Valid)
    (e : S ≃* ValidLieTypeIndex.Group ⟨.twistedE6 q, hv⟩) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup S) := by
  have hm : 0 < TwistTag.E6.order := by decide
  have hF := card_fieldOf q hm
  obtain ⟨φ⟩ := chevalleyBridgesAll.twistedE6 q hv (fieldOf q TwistTag.E6.order) hF
    (frobOf q TwistTag.E6.order) (frobOf_apply q TwistTag.E6.order)
  have hk : Nat.card (fieldOf q TwistTag.E6.order) = q.card ^ 2 := hF
  have hθq : ∀ c, (frobOf q TwistTag.E6.order) c = c ^ q.card := frobOf_apply q _
  have hq2 : 2 ≤ q.card := by
    rw [PrimePower.card_def]
    calc 2 ≤ q.p := q.prime_p.two_le
      _ = q.p ^ 1 := (pow_one _).symm
      _ ≤ q.p ^ q.exponent := Nat.pow_le_pow_right q.prime_p.pos q.exponent_pos
  have hK4 : 4 ≤ Nat.card (fieldOf q TwistTag.E6.order) := by
    rw [hk]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ q.card ^ 2 := Nat.pow_le_pow_left hq2 2
  have := two_le_pRank_three_twistedE6 (involutive_of_card_sq hk hθq) hK4 (e.trans φ.symm)
  omega

theorem two_le_pRank_three_exc_reeG2 {S : Type} [Group S] [Finite S] (m : ℕ)
    (hv : (LieTypeIndex.reeG2 m).Valid) (e : S ≃* ValidLieTypeIndex.Group ⟨.reeG2 m, hv⟩) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup S) := by
  have hmod := CFSG.RankThree.PartOne.CTP.reeTitsModel_reeG2 m ⟨hv, ⟨e⟩⟩
  obtain ⟨-, h3, hr⟩ := CFSG.SectionRank.smallReeModel_rank hmod
  omega


end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.ThreeRank
