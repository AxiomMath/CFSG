module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.BlockB.PLElem.RankFour
public import CFSG.LocalAnalysis.AGLEmbedding.BlockFactReductionsIV
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.NineThreeThreeCtx
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.TightCensus
public import CFSG.HardMathSupport.Curtis.Coordinator.BlockGlue
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.PLTypeHolds
import CFSG.RankThree.PartOne.N143.Inspect613Even
import CFSG.RankThree.PartTwo.Census.Carrier.SpinBBridge
public import CFSG.LocalAnalysis.AGLEmbedding.BlockParabThreeLeviMain
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.BlockB.PLElem.SURank

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.BlockB.PLElem

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbedding.ParabHub CFSG.QuasithinUnique
  CFSG.RankThreeCoreUniqueness.Helpers CFSG.Assembly.LowTwoRank CFSG.RankThree.PerfectCover
  CFSG.AGLEmbeddingD2 CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

@[expose] def IsBlockLieIndexE3 : TauCeti.LieTypeIndex → Prop
  | .A r q => q.card = 2 ∧ 4 ≤ r ∧ r ≤ 6
  | .twistedA r q => q.card = 2 ∧ r = 3
  | .B r q => q.card = 2 ∧ r = 3
  | .twistedD r q => q.card = 2 ∧ r = 4
  | _ => False

@[expose] def IsBlockQuotientE3 (X : Type) [Group X] : Prop :=
  (∃ d : TauCeti.ValidLieTypeIndex, IsBlockLieIndexE3 d.1 ∧
      Nonempty (X ≃* (TauCeti.CFSGIndex.lie d).Group)) ∨
    (∃ n : ℕ, (n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8) ∧ Nonempty (X ≃* alternatingGroup (Fin n))) ∨
    ∃ d : TauCeti.ValidLieTypeIndex, ((∃ q : TauCeti.PrimePower, q.card = 7 ∧ d.1 = .A 1 q) ∨
        (∃ q : TauCeti.PrimePower, q.card = 3 ∧ d.1 = .twistedA 2 q)) ∧
      Nonempty (X ≃* (TauCeti.CFSGIndex.lie d).Group)

section Free

theorem not_three_dvd_card_center_of_coprime {Y : Type} [Group Y] [Finite Y]
    (hY : CFSG.Open.IsQuasisimple Y)
    (hM : Nat.Coprime 3 (Nat.card (hopfMultiplier (Y ⧸ Subgroup.center Y)))) :
    ¬ 3 ∣ Nat.card (Subgroup.center Y) := by
  have : Group.IsPerfect Y := ⟨hY.1⟩
  set O : Subgroup Y := primeComplementCore (G := Y) 3 with hOdef
  have hO3 : ¬ 3 ∣ Nat.card O :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 (primeComplementCore_coprime 3)
  suffices hZO : Subgroup.center Y ≤ O from fun h => hO3 (h.trans (Subgroup.card_dvd_of_le hZO))
  rcases le_center_or_eq_top_of_normal_quasisimple hY O with hO | hO
  · have hY₁ : Group.IsPerfect (Y ⧸ O) :=
      Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective O)
    have hb := ker_eq_bot_of_coprime_hopfMultiplier hY₁ (quotCenterOfLeCenter hO)
      (quotCenterOfLeCenter_surjective hO) (ker_quotCenterOfLeCenter_le_center hO)
      (isPGroup_ker_quotCenterOfLeCenter hO) hM
    intro z hz
    have hmem := (mk_mem_ker_quotCenterOfLeCenter hO z).2 hz
    rw [hb, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hmem
    exact hmem
  · rw [hO]
    exact le_top

theorem charP_two_of_card_eq_two {F : Type} [Field F] [Finite F] (h : Nat.card F = 2 ^ 1) :
    CharP F 2 := by
  have := Fintype.ofFinite F
  exact charP_of_card_eq_prime_pow (f := 1) (by rw [← Nat.card_eq_fintype_card, h])

theorem four_le_pRank_of_quasisimple_model (hGA : CFSG.Open.GriessAllModelsStatement)
    {Y : Type} [Group Y] [Finite Y] (hY : CFSG.Open.IsQuasisimple Y) {t : StatedLieTag} {n : ℕ}
    (hc : StatedClassicalModel (Y ⧸ Subgroup.center Y) t n 2 1)
    (ht : (t = .PSL ∧ 8 ≤ n) ∨ (t = .PSp ∧ 4 ≤ n) ∨ (t = .POmegaPlus ∧ 4 ≤ n) ∨
      (t = .POmegaMinus ∧ 5 ≤ n)) :
    4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup Y) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have ht' : t = .PSL ∨ t = .PSp ∨ t = .POmegaPlus ∨ t = .POmegaMinus := by
    rcases ht with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
  have hZ := not_three_dvd_card_center_of_coprime hY
    (coprime_three_card_hopfMultiplier_of_model_two hGA hc ht')
  rw [← CFSG.SectionRank.pRank_quotient_eq (Subgroup.center Y) hZ]
  rcases ht with ⟨rfl, hn⟩ | ⟨rfl, hn⟩ | ⟨rfl, hn⟩ | ⟨rfl, hn⟩
  · obtain ⟨-, F, hF, hFfin, hcard, ⟨e⟩⟩ := hc
    have := charP_two_of_card_eq_two hcard
    have : Finite (StatedProj (StatedSL n F)) := Finite.of_equiv _ e.toEquiv
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv Nat.prime_three.one_lt e]
    exact psl_four_le_pRank_three hn
  · obtain ⟨-, F, hF, hFfin, hcard, ⟨e⟩⟩ := hc
    have := charP_two_of_card_eq_two hcard
    have : Finite (StatedProj (StatedSp n F)) := Finite.of_equiv _ e.toEquiv
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv Nat.prime_three.one_lt e]
    exact psp_four_le_pRank_three hn
  · obtain ⟨-, F, hF, hFfin, hcard, ⟨e⟩⟩ := hc
    have := charP_two_of_card_eq_two hcard
    have : Finite (StatedProj (StatedOmega (StatedQuadPlus n F))) := Finite.of_equiv _ e.toEquiv
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv Nat.prime_three.one_lt e]
    exact omegaPlus_four_le_pRank_three hn
  · obtain ⟨-, F, hF, hFfin, hcard, b, c, -, ⟨e⟩⟩ := hc
    have := charP_two_of_card_eq_two hcard
    have : Finite (StatedProj (StatedOmega (StatedQuadMinus n F b c))) :=
      Finite.of_equiv _ e.toEquiv
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv Nat.prime_three.one_lt e]
    exact omegaMinus_four_le_pRank_three hn b c

theorem isBlockLieIndexE3_of_pRank (hGA : CFSG.Open.GriessAllModelsStatement) {Y : Type}
    [Group Y] [Finite Y] (hY : CFSG.Open.IsQuasisimple Y)
    (hr : CFSG.Open.pRank 3 (⊤ : Subgroup Y) ≤ 3) (d : TauCeti.ValidLieTypeIndex)
    (hd : IsClassicalOrG2IndexTwo d.1)
    (e : Y ⧸ Subgroup.center Y ≃* (TauCeti.CFSGIndex.lie d).Group) : IsBlockLieIndexE3 d.1 := by
  obtain ⟨d, hv⟩ := d
  cases d with
  | A r q =>
    change q.card = 2 at hd
    obtain ⟨hp, hf⟩ := primePower_eq_of_card_eq Nat.prime_two hd
    have hr4 : 4 ≤ r := by
      have hv' := (TauCeti.LieTypeIndex.valid_iff _).1 hv
      simp only [TauCeti.LieTypeIndex.inStandardRange_iff,
        TauCeti.LieTypeIndex.isDuplicateRepresentative_iff, hd] at hv'
      by_contra h
      interval_cases r <;> simp_all
    refine ⟨hd, hr4, ?_⟩
    by_contra hr6
    have h := CFSG.RankThree.PartOne.N143.statedClassicalModel_of_isoLie_A hv e
    rw [hp, hf] at h
    have := four_le_pRank_of_quasisimple_model hGA hY h (Or.inl ⟨rfl, by omega⟩)
    omega
  | twistedA r q =>
    change q.card = 2 at hd
    obtain ⟨hp, hf⟩ := primePower_eq_of_card_eq Nat.prime_two hd
    have hr3' : 3 ≤ r := by
      have hv' := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
        ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
      by_contra h
      interval_cases r <;> simp_all
    refine ⟨hd, ?_⟩
    by_contra hr3
    have hr4 : 4 ≤ r := by omega
    have h := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e
    rw [hp, hf] at h
    have := four_le_pRank_of_quasisimple_psu hGA hY (by omega) h
    omega
  | B r q =>
    change q.card = 2 at hd
    obtain ⟨hp, hf⟩ := primePower_eq_of_card_eq Nat.prime_two hd
    have hr3' : 3 ≤ r := by
      have hv' := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
        ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
      by_contra h
      interval_cases r <;> simp_all
    refine ⟨hd, ?_⟩
    by_contra hr3
    have hr4 : 4 ≤ r := by omega
    have h := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even r q hv hp
      (by omega) e
    rw [hp, hf] at h
    have := four_le_pRank_of_quasisimple_model hGA hY h (Or.inr (Or.inl ⟨rfl, by omega⟩))
    omega
  | C r q => exact hd.elim
  | D r q =>
    change q.card = 2 at hd
    obtain ⟨hp, hf⟩ := primePower_eq_of_card_eq Nat.prime_two hd
    have h := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD_even r q hv hp e
    rw [hp, hf] at h
    have hr4 : 4 ≤ r := h.1.2.2
    have := four_le_pRank_of_quasisimple_model hGA hY h (Or.inr (Or.inr (Or.inl ⟨rfl, hr4⟩)))
    omega
  | twistedD r q =>
    change q.card = 2 at hd
    obtain ⟨hp, hf⟩ := primePower_eq_of_card_eq Nat.prime_two hd
    have hv' : 4 ≤ r := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
      ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
    refine ⟨hd, ?_⟩
    by_contra hr4
    have h := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD_even r q hv hp e
    rw [hp, hf] at h
    have := four_le_pRank_of_quasisimple_model hGA hY h
      (Or.inr (Or.inr (Or.inr ⟨rfl, by omega⟩)))
    omega
  | G2 q =>
    change q.card = 2 at hd
    have hq3 : 3 ≤ q.card :=
      (TauCeti.LieTypeIndex.inStandardRange_iff _).1 ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
    omega
  | _ => exact hd.elim

theorem not_three_dvd_card_center_of_indexTwo (hGA : CFSG.Open.GriessAllModelsStatement)
    {Y : Type} [Group Y] [Finite Y] (hY : CFSG.Open.IsQuasisimple Y)
    (hr : CFSG.Open.pRank 3 (⊤ : Subgroup Y) ≤ 3) (d : TauCeti.ValidLieTypeIndex)
    (hd : IsClassicalOrG2IndexTwo d.1)
    (e : Y ⧸ Subgroup.center Y ≃* (TauCeti.CFSGIndex.lie d).Group) :
    ¬ 3 ∣ Nat.card (Subgroup.center Y) := by
  obtain ⟨t, n, ht, hc⟩ := exists_model_of_indexTwo d hd e
  by_cases htu : t = .PSU
  · subst htu
    have hn4 : n ≤ 4 := by
      by_contra h5
      have := four_le_pRank_of_quasisimple_psu hGA hY (by omega) hc
      omega
    obtain ⟨⟨-, -, hn3, hne⟩, -⟩ := id hc
    have hn : n = 4 := by
      by_contra h4
      exact hne (by rw [show n = 3 by omega]; rfl)
    refine not_three_dvd_card_center_of_coprime hY ?_
    obtain ⟨e16, he16, hcard⟩ := card_hopfMultiplier_of_model_psu_two hGA hc
    rw [hcard, hn, show Nat.gcd 4 3 = 1 by norm_num, one_mul]
    exact Nat.Coprime.coprime_dvd_right he16 (by norm_num)
  · have ht' : t = .PSL ∨ t = .PSp ∨ t = .POmegaPlus ∨ t = .POmegaMinus := by
      rcases ht with h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h))
      · exact absurd h htu
    exact not_three_dvd_card_center_of_coprime hY
      (coprime_three_card_hopfMultiplier_of_model_two hGA hc ht')

variable {G : Type} [Group G] [Finite G]

theorem alt_of_nineThreeThree (hT : CitedBlockTransvectionPLType) {M S L : Subgroup G}
    (hK : Open.IsKGroup ↥M) (hA : Asc81bHyp M S) (hL : IsWeakSBlock M S L)
    (hX : ¬ InClassXBlock L) (hS : ¬ IsSylowTwoOf (S ⊓ L) L) (h3 : NineThreeThree M S L)
    (hsolv : BlockPLThreeSolv M S L) :
    ∃ N : ℕ, (N = 5 ∨ N = 6) ∧ Nonempty (↥(barM M L) ≃* alternatingGroup (Fin N)) := by
  obtain ⟨hOrth, hU4, -, -, hA8⟩ := hT G M S L hK hA hL hX hS h3
  have hno : ¬ ∃ Y : Subgroup ↥(blockPL M S L), ⁅Y, Y⁆ = Y ∧ 3 ∣ Nat.card Y := by
    rintro ⟨Y, hYp, hY3⟩
    refine hsolv (Y.map (blockPL M S L).subtype) (fun x ⟨y, _, hy⟩ => hy ▸ y.2) ?_ ?_
    · rw [← Subgroup.map_commutator, hYp]
    · rw [← Nat.card_congr (Y.equivMapOfInjective (blockPL M S L).subtype
        (blockPL M S L).subtype_injective).toEquiv]
      exact hY3
  rcases h3.2.1 with ⟨d, ⟨m, q, hq, hd⟩, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
  · exfalso
    apply hno
    rcases hd with hd | hd | ⟨rfl, hd⟩
    · obtain ⟨d', ⟨q', hq', hd'⟩, ⟨φ⟩⟩ := hOrth m d ⟨q, hq, Or.inl hd⟩ ⟨e⟩
      have hm : 4 ≤ m := by
        have h := d.2
        rw [hd] at h
        exact (TauCeti.LieTypeIndex.inStandardRange_iff _).1
          ((TauCeti.LieTypeIndex.valid_iff _).1 h).1
      exact exists_perfect_of_B_quotient (k := m - 1) (by omega) ⟨q', hq', hd'⟩ φ
    · obtain ⟨d', ⟨q', hq', hd'⟩, ⟨φ⟩⟩ := hOrth m d ⟨q, hq, Or.inr hd⟩ ⟨e⟩
      have hm : 4 ≤ m := by
        have h := d.2
        rw [hd] at h
        exact (TauCeti.LieTypeIndex.inStandardRange_iff _).1
          ((TauCeti.LieTypeIndex.valid_iff _).1 h).1
      exact exists_perfect_of_B_quotient (k := m - 1) (by omega) ⟨q', hq', hd'⟩ φ
    · obtain ⟨e6⟩ := hU4 d ⟨q, hq, hd⟩ ⟨e⟩
      exact exists_perfect_of_perm_six_quotient
        (nonempty_quotient_pCore_mulEquiv_of_bot e6 pCore_perm_six_eq_bot).some
  · rcases hn with rfl | rfl | rfl
    · exact ⟨5, Or.inl rfl, ⟨e⟩⟩
    · exact ⟨6, Or.inr rfl, ⟨e⟩⟩
    · exfalso
      apply hno
      obtain ⟨e6⟩ := hA8 ⟨e⟩
      exact exists_perfect_of_perm_six_quotient
        (nonempty_quotient_pCore_mulEquiv_of_bot e6 pCore_perm_six_eq_bot).some

theorem pRank_barM_top_le {M S L : Subgroup G} (hL : IsWeakSBlock M S L) :
    CFSG.Open.pRank 3 (⊤ : Subgroup ↥(barM M L)) ≤ CFSG.Open.pRank 3 M := by
  rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup,
    pRank_barM_eq Nat.prime_three (by norm_num) M L hL.le]
  exact CFSG.SectionRank.pRank_mono (by norm_num) hL.le

end Free

section Census


theorem parabolicQuotientE3_of (hGA : CFSG.Open.GriessAllModelsStatement) {Y : Type} [Group Y]
    [Finite Y] (hY : CFSG.Open.IsQuasisimple Y) (hcl : IsClassicalTwoOrG2 (Y ⧸ Subgroup.center Y))
    (hr : CFSG.Open.pRank 3 (⊤ : Subgroup Y) ≤ 3) (T J : Subgroup Y) (hT : IsSylowTwoOf T ⊤)
    (hNJ : Subgroup.normalizer (T : Set Y) ≤ J) (hJ : J ≠ Subgroup.normalizer (T : Set Y))
    (hperf : ∀ U : Subgroup Y, U ≤ J → ⁅U, U⁆ = U → Nat.Coprime 3 (Nat.card U)) :
    ((∃ d : TauCeti.ValidLieTypeIndex, IsBlockLieIndexE3 d.1 ∧
        Nonempty (Y ⧸ Subgroup.center Y ≃* (TauCeti.CFSGIndex.lie d).Group)) ∧
      ¬ 3 ∣ Nat.card (Subgroup.center Y)) ∨
    (∃ n : ℕ, (n = 5 ∨ n = 6 ∨ n = 8) ∧
      Nonempty (Y ⧸ Subgroup.center Y ≃* alternatingGroup (Fin n))) ∨
    ∃ d : TauCeti.ValidLieTypeIndex, ((∃ q : TauCeti.PrimePower, q.card = 7 ∧ d.1 = .A 1 q) ∨
        (∃ q : TauCeti.PrimePower, q.card = 3 ∧ d.1 = .twistedA 2 q)) ∧
      Nonempty (Y ⧸ Subgroup.center Y ≃* (TauCeti.CFSGIndex.lie d).Group) := by
  obtain ⟨S, rfl⟩ := exists_sylow_of_isSylowTwoOf_top hT
  obtain ⟨hTb, hNb, hJb, hperfb⟩ := map_overgroup_of_central
    (QuotientGroup.mk'_surjective (Subgroup.center Y)) (QuotientGroup.ker_mk' _).le S hNJ hJ hperf
  rcases kFactParabolicThreeCensus _ hcl _ _ hTb hNb hJb hperfb with ⟨d, hd, ⟨e⟩⟩ | hsmall
  · exact Or.inl ⟨⟨d, isBlockLieIndexE3_of_pRank hGA hY hr d hd e, ⟨e⟩⟩,
      not_three_dvd_card_center_of_indexTwo hGA hY hr d hd e⟩
  · exact Or.inr hsmall

variable {G : Type} [Group G] [Finite G]

theorem blockQuotientE3_of (hGA : CFSG.Open.GriessAllModelsStatement)
    (hT : CitedBlockTransvectionPLType) {M S L : Subgroup G} (hK : Open.IsKGroup ↥M)
    (hA : Asc81bHyp M S) (hL : IsWeakSBlock M S L) (hX : ¬ InClassXBlock L)
    (hS : ¬ IsSylowTwoOf (S ⊓ L) L) (hconc : NineThreeConclusion M S L)
    (hsolv : BlockPLThreeSolv M S L) (hr3 : CFSG.Open.pRank 3 M ≤ 3) :
    IsBlockQuotientE3 (↥(barM M L) ⧸ Subgroup.center ↥(barM M L)) := by
  have hrY := (pRank_barM_top_le hL).trans hr3
  have hperf : ∀ W : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), W ≤ blockPL M S L → ⁅W, W⁆ = W →
      Nat.Coprime 3 (Nat.card W) := fun W hW hWp =>
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 (hsolv W hW hWp)
  rcases hconc with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8
  · exact absurd h1 hX
  · obtain ⟨T₁, hT₁, hN, hne, hperf'⟩ := exists_parabolic_three_of_nineThreeTwo hA hL h2 hS hperf
    rcases parabolicQuotientE3_of hGA hL.component.2.2 h2.1 hrY T₁ _ hT₁ hN hne hperf' with
      ⟨hd, -⟩ | ⟨n, hn, he⟩ | hd
    · exact Or.inl hd
    · exact Or.inr (Or.inl ⟨n, by omega, he⟩)
    · exact Or.inr (Or.inr hd)
  · obtain ⟨N, hN, ⟨e⟩⟩ := alt_of_nineThreeThree hT hK hA hL hX hS h3 hsolv
    exact Or.inr (Or.inl ⟨N, by omega, quotCenterEquivAlt (by omega) e⟩)
  · obtain ⟨-, -, he, -⟩ := h4
    exact Or.inr (Or.inl ⟨6, by omega, he⟩)
  · obtain ⟨-, ⟨e⟩, -⟩ := h5
    exact Or.inr (Or.inl ⟨7, by omega, quotCenterEquivAlt (by omega) e⟩)
  · obtain ⟨n, hn4, ⟨e⟩⟩ := NineThreeSix.le_four h6 hsolv
    have h5 := five_le_of_quasisimple_cover_alt hL.le hL.perfect hL.component.2.2 e
    exact Or.inr (Or.inl ⟨2 * n, by omega, ⟨e⟩⟩)
  · obtain ⟨n, hn4, ⟨e⟩⟩ := NineThreeSeven.le_four h7 hsolv
    have hperfL : Group.IsPerfect ↥(barM M L) :=
      Subgroup.isPerfect_iff.mpr (barM_perfect hL.le hL.perfect)
    have : Nontrivial (↥(barM M L) ⧸ Subgroup.center ↥(barM M L)) :=
      (hL.component.2.2).2.toNontrivial
    have : Nontrivial ↥(barM M L) :=
      (QuotientGroup.mk_surjective (s := Subgroup.center ↥(barM M L))).nontrivial
    have h5 : 5 ≤ 4 * n := five_le_of_perfect_alt (Group.isPerfect_def.mp hperfL) e
    have hrk := CFSG.SectionRank.pRank_top_eq_of_mulEquiv Nat.prime_three.one_lt e
    have hn' : n = 2 := by
      by_contra hn2
      have h12 : 12 ≤ 4 * n := by omega
      have := CFSG.RankThree.PartTwo.Sec19.Item19Res3Proof.four_le_pRank_alternatingGroup h12
      omega
    subst hn'
    exact Or.inr (Or.inl ⟨4 * 2, by omega, quotCenterEquivAlt (by omega) e⟩)
  · exact absurd h8 (fun h => not_nineThreeEight h hsolv)

end Census

section Centre


variable {G : Type} [Group G] [Finite G]

theorem card_center_eq_three_of_dvd_of (hGA : CFSG.Open.GriessAllModelsStatement)
    (hT : CitedBlockTransvectionPLType) {M S L : Subgroup G} (hK : Open.IsKGroup ↥M)
    (hA : Asc81bHyp M S) (hL : IsWeakSBlock M S L) (hX : ¬ InClassXBlock L)
    (hS : ¬ IsSylowTwoOf (S ⊓ L) L) (hconc : NineThreeConclusion M S L)
    (hsolv : BlockPLThreeSolv M S L) (hr3 : CFSG.Open.pRank 3 M ≤ 3)
    (h3 : 3 ∣ Nat.card (Subgroup.center ↥(barM M L))) :
    Nat.card (Subgroup.center ↥(barM M L)) = 3 ∧
      Nonempty (↥(barM M L) ⧸ Subgroup.center ↥(barM M L) ≃* alternatingGroup (Fin 6)) := by
  have hrY := (pRank_barM_top_le hL).trans hr3
  have hperf : ∀ W : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), W ≤ blockPL M S L → ⁅W, W⁆ = W →
      Nat.Coprime 3 (Nat.card W) := fun W hW hWp =>
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 (hsolv W hW hWp)
  have hodd := CFSG.HardMathSupport.Curtis.Coordinator.odd_card_center_barM_of_isWeakSBlock hL
  have hpos : 0 < Nat.card (Subgroup.center ↥(barM M L)) := Nat.card_pos
  have hperfY : Group.IsPerfect ↥(barM M L) := ⟨hL.component.2.2.1⟩
  have halt : ∀ m : ℕ, 5 ≤ m →
      (↥(barM M L) ⧸ Subgroup.center ↥(barM M L) ≃* alternatingGroup (Fin m)) →
      Nat.card (Subgroup.center ↥(barM M L)) ∣ if m = 6 ∨ m = 7 then 6 else 2 := by
    intro m hm e
    have h := card_ker_dvd_of_alt hperfY (QuotientGroup.mk'_surjective _)
      (QuotientGroup.ker_mk' (Subgroup.center ↥(barM M L))).le hm e
    rwa [QuotientGroup.ker_mk'] at h
  have hsix : Nonempty (↥(barM M L) ⧸ Subgroup.center ↥(barM M L) ≃* alternatingGroup (Fin 6)) →
      Nat.card (Subgroup.center ↥(barM M L)) = 3 ∧
        Nonempty (↥(barM M L) ⧸ Subgroup.center ↥(barM M L) ≃* alternatingGroup (Fin 6)) := by
    rintro ⟨e⟩
    refine ⟨?_, ⟨e⟩⟩
    have hd := halt 6 (by norm_num) e
    rw [if_pos (Or.inl rfl)] at hd
    have hk6 := Nat.le_of_dvd (by norm_num) hd
    obtain ⟨j, hj⟩ := hodd
    omega
  have htwo : ∀ m : ℕ, 5 ≤ m → m ≠ 6 → m ≠ 7 →
      (↥(barM M L) ⧸ Subgroup.center ↥(barM M L) ≃* alternatingGroup (Fin m)) → False := by
    intro m hm h6 h7 e
    have hd := halt m hm e
    rw [if_neg (by omega)] at hd
    have hk2 := Nat.le_of_dvd (by norm_num) hd
    omega
  have hcz : ∀ N : ℕ, 5 ≤ N → (↥(barM M L) ≃* alternatingGroup (Fin N)) → False := by
    intro N hN e
    have hb := center_eq_bot_of_alt hN e
    rw [hb, Subgroup.card_bot] at h3
    norm_num at h3
  rcases hconc with h1 | h2 | h3' | h4 | h5 | h6 | h7 | h8
  · exact absurd h1 hX
  · obtain ⟨T₁, hT₁, hN, hne, hperf'⟩ := exists_parabolic_three_of_nineThreeTwo hA hL h2 hS hperf
    rcases parabolicQuotientE3_of hGA hL.component.2.2 h2.1 hrY T₁ _ hT₁ hN hne hperf' with
      ⟨-, hZ⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨d, hd, ⟨e⟩⟩
    · exact absurd h3 hZ
    · rcases hn with rfl | rfl | rfl
      · exact (htwo 5 (by norm_num) (by norm_num) (by norm_num) e).elim
      · exact hsix ⟨e⟩
      · exact (htwo 8 (by norm_num) (by norm_num) (by norm_num) e).elim
    · exfalso
      refine not_three_dvd_card_center_of_coprime hL.component.2.2 ?_ h3
      rcases hd with ⟨q, hq, hd'⟩ | ⟨q, hq, hd'⟩
      · obtain ⟨dd, hv⟩ := d
        simp only at hd'
        subst hd'
        obtain ⟨hp, hf⟩ := primePower_eq_of_card_eq Nat.prime_seven hq
        have hc := CFSG.RankThree.PartOne.N143.statedClassicalModel_of_isoLie_A hv e
        rw [hp, hf] at hc
        rw [card_hopfMultiplier_of_statedClassicalModel hGA hc]
        decide
      · obtain ⟨dd, hv⟩ := d
        simp only at hd'
        subst hd'
        obtain ⟨hp, hf⟩ := primePower_eq_of_card_eq Nat.prime_three hq
        have hc := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv e
        rw [hp, hf] at hc
        rw [card_hopfMultiplier_of_statedClassicalModel hGA hc]
        decide
  · obtain ⟨N, hN, ⟨e⟩⟩ := alt_of_nineThreeThree hT hK hA hL hX hS h3' hsolv
    exact (hcz N (by omega) e).elim
  · obtain ⟨-, hZ, he, -⟩ := h4
    exact ⟨hZ, he⟩
  · obtain ⟨-, ⟨e⟩, -⟩ := h5
    exact (hcz 7 (by norm_num) e).elim
  · obtain ⟨n, hn4, ⟨e⟩⟩ := NineThreeSix.le_four h6 hsolv
    have h5 := five_le_of_quasisimple_cover_alt hL.le hL.perfect hL.component.2.2 e
    have hn : n = 3 ∨ n = 4 := by omega
    rcases hn with rfl | rfl
    · exact hsix ⟨e⟩
    · exact (htwo (2 * 4) (by norm_num) (by norm_num) (by norm_num) e).elim
  · obtain ⟨n, -, ⟨e⟩⟩ := NineThreeSeven.le_four h7 hsolv
    have hperfL : Group.IsPerfect ↥(barM M L) :=
      Subgroup.isPerfect_iff.mpr (barM_perfect hL.le hL.perfect)
    have : Nontrivial (↥(barM M L) ⧸ Subgroup.center ↥(barM M L)) :=
      (hL.component.2.2).2.toNontrivial
    have : Nontrivial ↥(barM M L) :=
      (QuotientGroup.mk_surjective (s := Subgroup.center ↥(barM M L))).nontrivial
    exact (hcz (4 * n) (five_le_of_perfect_alt (Group.isPerfect_def.mp hperfL) e) e).elim
  · exact absurd h8 (fun h => not_nineThreeEight h hsolv)

end Centre

section Closed


variable {G : Type} [Group G] [Finite G]

theorem blockQuotientE3 {M S L : Subgroup G} (hK : Open.IsKGroup ↥M) (hA : Asc81bHyp M S)
    (hL : IsWeakSBlock M S L) (hX : ¬ InClassXBlock L) (hS : ¬ IsSylowTwoOf (S ⊓ L) L)
    (hconc : NineThreeConclusion M S L) (hsolv : BlockPLThreeSolv M S L)
    (hr3 : CFSG.Open.pRank 3 M ≤ 3) :
    IsBlockQuotientE3 (↥(barM M L) ⧸ Subgroup.center ↥(barM M L)) :=
  blockQuotientE3_of CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds
    CFSG.HardMathSupport.Curtis.UnitaryLevi.citedBlockTransvectionPLType_holds hK hA hL hX hS
    hconc hsolv hr3

theorem card_center_eq_three_of_dvd {M S L : Subgroup G} (hK : Open.IsKGroup ↥M)
    (hA : Asc81bHyp M S) (hL : IsWeakSBlock M S L) (hX : ¬ InClassXBlock L)
    (hS : ¬ IsSylowTwoOf (S ⊓ L) L) (hconc : NineThreeConclusion M S L)
    (hsolv : BlockPLThreeSolv M S L) (hr3 : CFSG.Open.pRank 3 M ≤ 3)
    (h3 : 3 ∣ Nat.card (Subgroup.center ↥(barM M L))) :
    Nat.card (Subgroup.center ↥(barM M L)) = 3 ∧
      Nonempty (↥(barM M L) ⧸ Subgroup.center ↥(barM M L) ≃* alternatingGroup (Fin 6)) :=
  card_center_eq_three_of_dvd_of CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds
    CFSG.HardMathSupport.Curtis.UnitaryLevi.citedBlockTransvectionPLType_holds hK hA hL hX hS
    hconc hsolv hr3 h3

theorem card_inf_centralizer_eq_three_of_dvd {M S L : Subgroup G} (hK : Open.IsKGroup ↥M)
    (hA : Asc81bHyp M S) (hL : IsWeakSBlock M S L) (hX : ¬ InClassXBlock L)
    (hS : ¬ IsSylowTwoOf (S ⊓ L) L) (hconc : NineThreeConclusion M S L)
    (hsolv : BlockPLThreeSolv M S L) (hr3 : CFSG.Open.pRank 3 M ≤ 3)
    (h3 : 3 ∣ Nat.card (barM M L ⊓
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) : Subgroup _)) :
    Nat.card (barM M L ⊓
        Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) : Subgroup _) = 3 ∧
      Nonempty (↥(barM M L) ⧸ Subgroup.center ↥(barM M L) ≃* alternatingGroup (Fin 6)) := by
  rw [card_inf_centralizer_eq_card_center] at h3 ⊢
  exact card_center_eq_three_of_dvd hK hA hL hX hS hconc hsolv hr3 h3

end Closed

end CFSG.LocalAnalysis.RankThreeTheoremC.BlockB.PLElem
