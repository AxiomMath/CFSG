module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.ThreeRankClsIndex
public import CFSG.LieType.SeitzGeneration.ExcParabolicReeF4
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.ThreeRankExc
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.ThreeRankTits
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.ThreeRankTwD4
public import CFSG.RankThree.PartOne.KLC.TwF4

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.Open TauCeti CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.ThreeRank
  CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.ThreeRankCls

set_option linter.unusedSectionVars false

section Exceptional

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.TauCetiBridge
  CFSG.TauCetiBridge.Even


theorem two_le_pRank_three_of_untwisted_exceptional {S : Type} [Group S] [Finite S]
    (q : PrimePower) (d : ValidLieTypeIndex)
    (hd : (d.1 = .G2 q) ∨ (d.1 = .F4 q) ∨ (d.1 = .E6 q) ∨ (d.1 = .E7 q) ∨ (d.1 = .E8 q))
    (e : S ≃* ValidLieTypeIndex.Group d) : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup S) := by
  obtain ⟨i, hv⟩ := d
  rcases hd with rfl | rfl | rfl | rfl | rfl
  · obtain ⟨K, _, _, ⟨φ⟩⟩ := exists_untwisted_model chevalleyBridgesAll.g2 q hv e
    have := two_le_pRank_three_adjointQuotient_G2 (K := K)
    rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) φ] at this
    exact this
  · obtain ⟨K, _, _, ⟨φ⟩⟩ := exists_untwisted_model chevalleyBridgesAll.f4 q hv e
    have := four_le_pRank_three_adjointQuotient_any (τ := .F4) (Or.inl rfl) (K := K)
    rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) φ] at this
    omega
  · obtain ⟨K, _, _, ⟨φ⟩⟩ := exists_untwisted_model chevalleyBridgesAll.e6 q hv e
    have := four_le_pRank_three_adjointQuotient_any (τ := .E6) (Or.inr (Or.inl rfl)) (K := K)
    rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) φ] at this
    omega
  · obtain ⟨K, _, _, ⟨φ⟩⟩ := exists_untwisted_model chevalleyBridgesAll.e7 q hv e
    have := four_le_pRank_three_adjointQuotient_any (τ := .E7) (Or.inr (Or.inr (Or.inl rfl)))
      (K := K)
    rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) φ] at this
    omega
  · obtain ⟨K, _, _, ⟨φ⟩⟩ := exists_untwisted_model chevalleyBridgesAll.e8 q hv e
    have := four_le_pRank_three_adjointQuotient_any (τ := .E8) (Or.inr (Or.inr (Or.inr rfl)))
      (K := K)
    rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) φ] at this
    omega

theorem two_le_pRank_three_of_twistedE6 {S : Type} [Group S] [Finite S] (q : PrimePower)
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
  exact two_le_pRank_three_twistedE6 (involutive_of_card_sq hk hθq) hK4 (e.trans φ.symm)

theorem two_le_pRank_three_of_trialityD4 {S : Type} [Group S] [Finite S] (q : PrimePower)
    (hv : (LieTypeIndex.trialityD4 q).Valid)
    (e : S ≃* ValidLieTypeIndex.Group ⟨.trialityD4 q, hv⟩) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup S) := by
  have hm : 0 < TwistTag.D4.order := by decide
  have hF := card_fieldOf q hm
  obtain ⟨φ⟩ := chevalleyBridgesAll.trialityD4 q hv (fieldOf q TwistTag.D4.order) hF
    (frobOf q TwistTag.D4.order) (frobOf_apply q TwistTag.D4.order)
  have hk : Nat.card (fieldOf q TwistTag.D4.order) = q.card ^ 3 := hF
  have hq2 : 2 ≤ q.card := by
    rw [PrimePower.card_def]
    calc 2 ≤ q.p := q.prime_p.two_le
      _ = q.p ^ 1 := (pow_one _).symm
      _ ≤ q.p ^ q.exponent := Nat.pow_le_pow_right q.prime_p.pos q.exponent_pos
  exact two_le_pRank_three_twistedD4 hq2 hk (frobOf_apply q TwistTag.D4.order)
    (e.trans φ.symm)

theorem two_le_pRank_three_of_reeG2 {S : Type} [Group S] [Finite S] (m : ℕ)
    (hv : (LieTypeIndex.reeG2 m).Valid) (e : S ≃* ValidLieTypeIndex.Group ⟨.reeG2 m, hv⟩) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup S) := by
  have hmod := CFSG.RankThree.PartOne.CTP.reeTitsModel_reeG2 m ⟨hv, ⟨e⟩⟩
  obtain ⟨-, h3, hr⟩ := CFSG.SectionRank.smallReeModel_rank hmod
  omega

theorem two_le_pRank_three_of_tits {S : Type} [Group S] [Finite S]
    (hv : (LieTypeIndex.tits).Valid) (e : S ≃* ValidLieTypeIndex.Group ⟨.tits, hv⟩) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup S) := by
  have hmod := CFSG.RankThree.PartOne.CTP.reeTitsModel_tits ⟨hv, ⟨e⟩⟩
  obtain ⟨K, _, _, _, hK, ⟨φ⟩⟩ := CFSG.SectionRank.exists_mulEquiv_titsGroup_of_model hmod
  obtain ⟨x, y, h, hx, -, hz, hzx, hzy, -⟩ := CFSG.SectionRank.Tits_sylow3_cubic_witness hK
  have := two_le_pRank_three_of_extraspecial hx hz hzx hzy
  rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) φ] at this
  omega

section ReeF4

open CFSG.LieType.Ree CFSG.RankThree.PartOne.KLC CFSG.RankThree.PartOne.KLR
  CFSG.LieType.SeitzGeneration

theorem two_le_pRank_three_of_reeF4 {S : Type} [Group S] [Finite S] (m : ℕ)
    (hv : (LieTypeIndex.reeF4 m).Valid) (e : S ≃* ValidLieTypeIndex.Group ⟨.reeF4 m, hv⟩) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup S) := by
  obtain ⟨X, _, _, _, hm, hX, -, ⟨φ⟩⟩ := exists_reeGamma_equiv_cat hv
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite (ReeTag.F4.reeGamma X m) := Finite.of_equiv _ (e.trans φ).toEquiv
  obtain ⟨D⟩ := reeFrameData_nonempty (K := X) (L := AlgebraicClosure X) hX
  have : CharP (AlgebraicClosure X) 2 :=
    charP_of_injective_algebraMap (algebraMap X (AlgebraicClosure X)).injective 2
  have h3 : (3 : ℤ) ∣ 2 ^ (2 * m + 1) + 1 := by
    have hq : 2 ^ (2 * m + 1) % 3 = 2 := by
      rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
      norm_num
    have : 3 ∣ 2 ^ (2 * m + 1) + 1 := by omega
    exact_mod_cast this
  obtain ⟨Φ, hΦ, -, hΦF⟩ := torus_hom_phi2 (L := AlgebraicClosure X) D.isFrob Nat.prime_three
    (by norm_num) h3
  have h2 := two_le_pRank_reeGamma D wPhi2 Nat.prime_three (by norm_num) Φ hΦ hΦF
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top,
    ← CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) (e.trans φ)] at h2
  exact h2

end ReeF4

theorem three_rank_le_one_lie {S : Type} [Group S] [Finite S] (d : ValidLieTypeIndex)
    (e : S ≃* (CFSGIndex.lie d).Group) (hm3 : CFSG.Open.pRank 3 (⊤ : Subgroup S) ≤ 1) :
    (∃ q : PrimePower, q.p ≠ 3 ∧ d.1 = .A 1 q) ∨
      (∃ q : PrimePower, q.card % 3 = 2 ∧ d.1 = .A 2 q) ∨
      (∃ q : PrimePower, q.card % 3 = 1 ∧ d.1 = .twistedA 2 q) ∨ (∃ m : ℕ, d.1 = .suzuki m) := by
  obtain ⟨d, hv⟩ := d
  cases d with
  | A r q =>
    by_cases hA1 : r = 1 ∧ q.p ≠ 3
    · obtain ⟨rfl, hp⟩ := hA1
      exact Or.inl ⟨q, hp, rfl⟩
    by_cases hA2 : r = 2 ∧ q.card % 3 = 2
    · obtain ⟨rfl, hc⟩ := hA2
      exact Or.inr (Or.inl ⟨q, hc, rfl⟩)
    exact absurd (A_two_le_pRank_three hv e hA1 hA2) (by omega)
  | twistedA r q =>
    by_cases hA : r = 2 ∧ q.card % 3 = 1
    · obtain ⟨rfl, hc⟩ := hA
      exact Or.inr (Or.inr (Or.inl ⟨q, hc, rfl⟩))
    exact absurd (twistedA_two_le_pRank_three hv e hA) (by omega)
  | B r q => exact absurd (B_two_le_pRank_three hv e) (by omega)
  | C r q => exact absurd (C_two_le_pRank_three hv e) (by omega)
  | D r q => exact absurd (D_two_le_pRank_three hv e) (by omega)
  | twistedD r q => exact absurd (twistedD_two_le_pRank_three hv e) (by omega)
  | E6 q =>
    exact absurd (two_le_pRank_three_of_untwisted_exceptional q ⟨.E6 q, hv⟩ (Or.inr (Or.inr
      (Or.inl rfl))) e) (by omega)
  | E7 q =>
    exact absurd (two_le_pRank_three_of_untwisted_exceptional q ⟨.E7 q, hv⟩ (Or.inr (Or.inr
      (Or.inr (Or.inl rfl)))) e) (by omega)
  | E8 q =>
    exact absurd (two_le_pRank_three_of_untwisted_exceptional q ⟨.E8 q, hv⟩ (Or.inr (Or.inr
      (Or.inr (Or.inr rfl)))) e) (by omega)
  | F4 q =>
    exact absurd (two_le_pRank_three_of_untwisted_exceptional q ⟨.F4 q, hv⟩ (Or.inr (Or.inl rfl))
      e) (by omega)
  | G2 q =>
    exact absurd (two_le_pRank_three_of_untwisted_exceptional q ⟨.G2 q, hv⟩ (Or.inl rfl) e)
      (by omega)
  | twistedE6 q => exact absurd (two_le_pRank_three_of_twistedE6 q hv e) (by omega)
  | trialityD4 q => exact absurd (two_le_pRank_three_of_trialityD4 q hv e) (by omega)
  | suzuki m => exact Or.inr (Or.inr (Or.inr ⟨m, rfl⟩))
  | reeG2 m => exact absurd (two_le_pRank_three_of_reeG2 m hv e) (by omega)
  | reeF4 m => exact absurd (two_le_pRank_three_of_reeF4 m hv e) (by omega)
  | tits => exact absurd (two_le_pRank_three_of_tits hv e) (by omega)

end Exceptional

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
