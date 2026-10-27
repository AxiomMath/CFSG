module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.TRFrontier
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.TRMoveGen
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.TROne
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.TwoFixA6U33
import CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.AltSocle.BigVector
import CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.AltSocle.Fixed
import CFSG.LocalAnalysis.AGLEmbedding.AscEightFour
import CFSG.LocalAnalysis.AGLEmbedding.AscEightFive
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.PairSepAssembly
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.TRAssemble
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.TRResidues

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin

open CFSG.Open CFSG.AGLEmbedding CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
  CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank

section Types

variable {G : Type} [Group G] [Finite G]

@[expose] def PairTwoEngineBlock (M S L : Subgroup G) : Prop :=
  IsClassicalTwoOrG2 (↥(barM M L) ⧸ Subgroup.center ↥(barM M L)) ∧
    ∃ Q : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), IsSylowTwoOf Q (barM M L) ∧
      Q ≤ barM M (Subgroup.normalizer (S : Set G) ⊓ L)

omit [Finite G] in
theorem engineBlock_of_nineThreeTwo {M S L : Subgroup G} (h : NineThreeTwo M S L) :
    PairTwoEngineBlock M S L := by
  obtain ⟨hcl, ⟨-, T', hT', hnorm⟩, -⟩ := h
  exact ⟨hcl, T', hT', fun x hx => hnorm ⟨hT'.1 hx, Subgroup.le_normalizer hx⟩⟩

@[expose] def PairTwoBadShape2 (M S L : Subgroup G) : Prop :=
  (Open.pRank 3 L ≤ 1 ∨
    Nonempty (↥(barM M L) ⧸ Subgroup.center ↥(barM M L) ≃* alternatingGroup (Fin 8)) ∨
    IsL5Two (↥(barM M L) ⧸ Subgroup.center ↥(barM M L))) ∧ ¬ PairTwoEngineBlock M S L

theorem shape_of_census (hU : U33Atlas) (hL32 : L32Atlas) (hK3 : KFactNineThreeThreeBig)
    {M S L : Subgroup G} (hKM : Open.IsKGroup ↥M) (hA : Asc81bHyp M S) (hw : IsWeakSBlock M S L)
    (hnX : ¬ InClassXBlock L) (hnS : ¬ IsSylowTwoOf (S ⊓ L) L)
    (hZ : ¬ 3 ∣ Nat.card (barM M L ⊓
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) : Subgroup _))
    (hsolv : BlockPLThreeSolv M S L) (hc : BlockCensus M S L)
    (hbad : ¬ PairTwoBadShape2 M S L) :
    PairTwoAltSeven M L ∨ IsA6OrU33 ↥(barM M L) ∨ PairTwoEngineBlock M S L := by
  rcases hc with h4 | ⟨hr2, -, hrow⟩ | ⟨h7, h1216⟩ | hle1 | ⟨h23, hr3⟩ | ⟨hZ3, -⟩
  · exfalso
    rw [card_inf_centralizer_eq_card_center, h4.2.1] at hZ
    exact hZ (dvd_refl 3)
  · rcases hrow with hrow | h5
    · rcases hrow with hA6 | ⟨h5, hA7⟩ | hA8 | hU3
      · exact Or.inr (Or.inl (isA6OrU33_of_doubling hU hL32 hw hZ (by omega)
          (Or.inr (Or.inl hA6))))
      · exact Or.inl (Or.inr ⟨h5, hA7⟩)
      · by_cases ht : PairTwoEngineBlock M S L
        · exact Or.inr (Or.inr ht)
        · exact absurd ⟨Or.inr (Or.inl hA8), ht⟩ hbad
      · exact Or.inr (Or.inl (isA6OrU33_of_doubling hU hL32 hw hZ (by omega)
          (Or.inr (Or.inr hU3))))
    · by_cases ht : PairTwoEngineBlock M S L
      · exact Or.inr (Or.inr ht)
      · exact absurd ⟨Or.inr (Or.inr h5), ht⟩ hbad
  · refine Or.inl (Or.inl ?_)
    rcases h1216 with e | e
    · exact ⟨12, Or.inl rfl, e⟩
    · exact ⟨16, Or.inr rfl, e⟩
  · by_cases ht : PairTwoEngineBlock M S L
    · exact Or.inr (Or.inr ht)
    · exact absurd ⟨Or.inl hle1, ht⟩ hbad
  · rcases h23 with h2 | h3
    · exact Or.inr (Or.inr (engineBlock_of_nineThreeTwo h2))
    · exact absurd hsolv (hK3 G M S L hKM hA hw hnX hnS h3 hr3)
  · exact absurd hZ3 hZ

end Types



section Engine

variable {G : Type} [Group G] [Finite G]

theorem doubling_of_engineBlocks (hGN : GlaubermanNilesInput)
    (hCov : KFactParabolicCoverDoubling) (hK : KFactStrongThreeSolv) (hH29 : RankImageOne)
    {P : Sylow 3 G} {M A H R : Subgroup G} (hctx : PairStrongCtx P M A H R)
    (hev : PairEvenIndex M H) (hXb : CFSG.AGLEmbeddingD2.NoXBlockFor G) {L₁ L₂ : Subgroup G}
    (h₁ : IsWeakSBlock M (pCoreOf 2 H) L₁) (h₂ : IsWeakSBlock M (pCoreOf 2 H) L₂)
    (hne : barM M L₁ ≠ barM M L₂)
    (hk2 : ∀ L' : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L' →
      barM M L' = barM M L₁ ∨ barM M L' = barM M L₂)
    (t₁ : PairTwoEngineBlock M (pCoreOf 2 H) L₁) (t₂ : PairTwoEngineBlock M (pCoreOf 2 H) L₂)
    (hZ₁ : ¬ 3 ∣ Nat.card (barM M L₁ ⊓
      Subgroup.centralizer (barM M L₁ : Set (↥M ⧸ CFSG.pCore 2 ↥M)) : Subgroup _))
    (hZ₂ : ¬ 3 ∣ Nat.card (barM M L₂ ⊓
      Subgroup.centralizer (barM M L₂ : Set (↥M ⧸ CFSG.pCore 2 ↥M)) : Subgroup _))
    (h3₁ : 3 ∣ Nat.card (barM M L₁)) (h3₂ : 3 ∣ Nat.card (barM M L₂))
    (hrank : 2 < Open.pRank 3 L₁ + Open.pRank 3 L₂) :
    IsDoublingList (↥(barM M L₁) ⧸ Subgroup.center ↥(barM M L₁)) ∧
      IsDoublingList (↥(barM M L₂) ⧸ Subgroup.center ↥(barM M L₂)) := by
  obtain ⟨T, hT2, hQT, hNT, hT⟩ := hctx.exists_twoGroup_of_evenIndex hev
  have hNH := hctx.pair.normalizer_twoCore_H
  have hZ₁' : ¬ 3 ∣ Nat.card (Subgroup.center ↥(barM M L₁)) := by
    rwa [← card_inf_centralizer_eq_card_center]
  have hZ₂' : ¬ 3 ∣ Nat.card (Subgroup.center ↥(barM M L₂)) := by
    rwa [← card_inf_centralizer_eq_card_center]
  have hSyl := isSylowTwoOf_trX_of_sylow_le h₁ h₂ hne hk2 hT hQT hNH t₁.2 t₂.2
  have hmove := trBlocksMove_general hGN hH29 hK hctx hXb h₁ h₂ hne hk2 hT hNT hQT hSyl hZ₁' hZ₂'
    h3₁ h3₂ hrank
  exact doubling_of_trX hGN hCov hK hctx hXb h₁ h₂ hne hk2 hT hNT hQT hSyl hmove.1 hmove.2
    hZ₁' hZ₂' t₁.1 t₂.1 h3₁ h3₂ hrank

theorem false_of_isA6OrU33_block (hCF : CitedFive) (hat : U33Atlas) (hU : U33Facts)
    {P : Sylow 3 G} {M A H R : Subgroup G} (hctx : PairStrongCtx P M A H R)
    {L L' : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    (hL' : IsWeakSBlock M (pCoreOf 2 H) L') (hne : barM M L ≠ barM M L')
    (hrow : IsA6OrU33 ↥(barM M L)) (hr2 : 2 ≤ Open.pRank 3 L') : False := by
  have h86 : Asc81bEightSix :=
    asc81bEightSix_of_bhs CFSG.LocalAnalysis.RankThreeTheoremC.bhsLocalCStar_proved
  have hc := center_barM_eq_bot hU hrow
  obtain ⟨hrow', hn8⟩ := tightRow_of_isA6OrU33 hat hU hrow
  have hz : ¬ 3 ∣ Nat.card (barM M L ⊓
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) : Subgroup _) := by
    rw [card_inf_centralizer_eq_card_center, hc]
    simp
  obtain ⟨x, hx, hx1, -, hrk⟩ := exists_sep_of_tightRow' hCF hat h86 hctx hL hL' hne hz hr2 hrow'
    hc hn8
  exact hctx.esc.false_of_pureVector hctx.d1 hctx.beta hctx.strong hx hx1 hrk fun y hy _ =>
    (pairBlockFixed_of_A6U33 hCF hat hctx hL hrow hy).trans
      (Subgroup.card_dvd_of_le (inf_le_inf_right _ hL.le))

theorem pRank_le_two_of_isA6OrU33 (hSA : SmallRankAtlas) {M L : Subgroup G} (hLM : L ≤ M)
    (h : IsA6OrU33 ↥(barM M L)) : Open.pRank 3 L ≤ 2 := by
  rw [← pRank_barM_eq Nat.prime_three (by norm_num) M L hLM,
    CFSG.SectionRank.pRank_eq_pRank_top_subgroup (barM M L)]
  rcases h with he | h
  · obtain ⟨e⟩ := he
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv Nat.prime_three.one_lt e]
    have := pRank_three_alternating_le (N := 6)
    omega
  · exact hSA _ (Or.inr h)

theorem pRank_le_two_of_altSeven_row {M L : Subgroup G} (hLM : L ≤ M)
    (hZ : ¬ 3 ∣ Nat.card (barM M L ⊓
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) : Subgroup _))
    (e : ↥(barM M L) ⧸ Subgroup.center ↥(barM M L) ≃* alternatingGroup (Fin 7)) :
    Open.pRank 3 L ≤ 2 := by
  have h1 := pRank_top_quot_center_eq hLM hZ
  have h2 := CFSG.SectionRank.pRank_top_eq_of_mulEquiv Nat.prime_three.one_lt e
  have h3 := pRank_three_alternating_le (N := 7)
  omega

theorem false_of_cf_block (hCF : CitedFive) (hat : U33Atlas) (hU : U33Facts) (hJ : JordanPrimeCycle)
    (hnat : CFSG.HardMathSupport.Cooperstein.Coordinator.GF2EightFive)
    (hSA : SmallRankAtlas) {P : Sylow 3 G} {M A H R : Subgroup G}
    (hctx : PairStrongCtx P M A H R) {L L' : Subgroup G}
    (hL : IsWeakSBlock M (pCoreOf 2 H) L) (hL' : IsWeakSBlock M (pCoreOf 2 H) L')
    (hne : barM M L ≠ barM M L')
    (hZ : ¬ 3 ∣ Nat.card (barM M L ⊓
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) : Subgroup _))
    (hlowL : Open.pRank 3 L' ≤ 1 → Open.pRank 3 L ≤ 2 → False)
    (hcf : PairTwoAltSeven M L ∨ IsA6OrU33 ↥(barM M L)) : False := by
  rcases hcf with (⟨N, hN, ⟨e⟩⟩ | ⟨h5, ⟨e⟩⟩) | hrow
  ·
    have h86 : Asc81bEightSix :=
      asc81bEightSix_of_bhs CFSG.LocalAnalysis.RankThreeTheoremC.bhsLocalCStar_proved
    obtain ⟨x, hxV, hx1, hrk⟩ :=
      CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.AltSocle.exists_bigVector_of_alt' h86 hnat hctx hL
      (by rcases hN with rfl | rfl <;> norm_num) e
    refine hctx.esc.false_of_pureVector hctx.d1 hctx.beta hctx.strong hxV hx1
      (hrk.trans (CFSG.PreuniquenessRankFour.Helpers.pRank_mono 3 Nat.prime_three
        (le_inf inf_le_right (inf_le_left.trans hL.le)))) fun y hy _ => ?_
    exact (CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.AltSocle.fixed_of_alt_pair' h86 hJ hnat hctx hL hN e
      hy).trans
      (Subgroup.card_dvd_of_le (inf_le_inf_right _ hL.le))
  ·
    have hle := pRank_le_two_of_altSeven_row hL.le hZ e
    by_cases hlow : Open.pRank 3 L' ≤ 1
    · exact hlowL hlow hle
    · push Not at hlow
      have h2 : 2 ≤ Open.pRank 3 L := by
        have h1 := pRank_top_quot_center_eq hL.le hZ
        have h2 := CFSG.SectionRank.pRank_top_eq_of_mulEquiv Nat.prime_three.one_lt e
        have h3 := le_pRank_alternatingGroup_three (N := 7) (k := 2) (by norm_num)
        omega
      exact false_of_altSeven_aux hCF hat hJ hnat hctx hL hL' hne hZ (fun _ => by omega)
        (Or.inr ⟨h5, ⟨e⟩⟩)
  · by_cases hlow : Open.pRank 3 L' ≤ 1
    · exact hlowL hlow (pRank_le_two_of_isA6OrU33 hSA hL.le hrow)
    · push Not at hlow
      exact false_of_isA6OrU33_block hCF hat hU hctx hL hL' hne hrow (by omega)

end Engine

section Final

variable {G : Type} [Group G] [Finite G]

theorem isA6OrU33_or_rank_le_one (hat : U33Atlas) (hU : U33Facts) (hL32 : L32Atlas)
    {M S L : Subgroup G} (hw : IsWeakSBlock M S L)
    (hZ : ¬ 3 ∣ Nat.card (barM M L ⊓
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) : Subgroup _))
    (hd : IsDoublingList (↥(barM M L) ⧸ Subgroup.center ↥(barM M L))) :
    IsA6OrU33 ↥(barM M L) ∨ Open.pRank 3 L ≤ 1 := by
  have hrq := pRank_top_quot_center_eq hw.le hZ
  rcases hd with hL3 | hA6 | hU3
  · right
    have := pRank_top_le_one_of_card_168 (hL32 _ hL3)
    omega
  · left
    refine isA6OrU33_of_doubling hat hL32 hw hZ ?_ (Or.inr (Or.inl hA6))
    obtain ⟨e⟩ := hA6
    have h1 := CFSG.SectionRank.pRank_top_eq_of_mulEquiv Nat.prime_three.one_lt e
    have h2 := two_le_pRank_alternatingGroup_six
    omega
  · left
    refine isA6OrU33_of_doubling hat hL32 hw hZ ?_ (Or.inr (Or.inr hU3))
    have := (hU _ hU3).2
    omega

@[expose] def PairTwoBadShape2Residue : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (P : Sylow 3 G) (M A H R : Subgroup G),
    PairStrongCtx P M A H R → PairEvenIndex M H →
    ∀ L₁ L₂ : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L₁ → IsWeakSBlock M (pCoreOf 2 H) L₂ →
    barM M L₁ ≠ barM M L₂ →
    (∀ L' : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L' →
      barM M L' = barM M L₁ ∨ barM M L' = barM M L₂) →
    ¬ 3 ∣ Nat.card (barM M L₁ ⊓
      Subgroup.centralizer (barM M L₁ : Set (↥M ⧸ CFSG.pCore 2 ↥M)) : Subgroup _) →
    ¬ 3 ∣ Nat.card (barM M L₂ ⊓
      Subgroup.centralizer (barM M L₂ : Set (↥M ⧸ CFSG.pCore 2 ↥M)) : Subgroup _) →
    ∀ L ∈ ({L₁, L₂} : Set (Subgroup G)), ¬ PairTwoBadShape2 M (pCoreOf 2 H) L

theorem false_of_two_images (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (hΛ : KFactBlockInvertedThree) (hLF : LargeFieldParabolic) (h418 : Agl418)
    (hL27 : L2SevenRankOne) (hGN : GlaubermanNilesInput) (hCov : KFactParabolicCoverDoubling)
    (hK : KFactStrongThreeSolv) (hH29 : RankImageOne) (hCF : CitedFive) (hat : U33Atlas)
    (hU33 : U33Facts) (hJ : JordanPrimeCycle)
    (hnat : CFSG.HardMathSupport.Cooperstein.Coordinator.GF2EightFive) (hL32 : L32Atlas)
    (hSA : SmallRankAtlas) (hK3 : KFactNineThreeThreeBig) (hlow : ∀ (G : Type) [Group G] [Finite G]
        (P : Sylow 3 G) (M A H R : Subgroup G), PairStrongCtx P M A H R → ∀ L₁ L₂ : Subgroup G,
        IsWeakSBlock M (pCoreOf 2 H) L₁ → IsWeakSBlock M (pCoreOf 2 H) L₂ → barM M L₁ ≠ barM M L₂ →
        (∀ L' : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L' → barM M L' = barM M L₁ ∨ barM M L' =
        barM M L₂) → ¬ 3 ∣ Nat.card (barM M L₁ ⊓ Subgroup.centralizer (barM M L₁ : Set (↥M ⧸
        CFSG.pCore 2 ↥M)) : Subgroup _) → ¬ 3 ∣ Nat.card (barM M L₂ ⊓ Subgroup.centralizer (barM M
        L₂ : Set (↥M ⧸ CFSG.pCore 2 ↥M)) : Subgroup _) → Open.pRank 3 L₁ ≤ 1 → Open.pRank 3 L₂ ≤ 2 →
        False)
    (hbad : PairTwoBadShape2Residue) {P : Sylow 3 G} {M A H R : Subgroup G}
    (hctx : PairStrongCtx P M A H R) (hev : PairEvenIndex M H) {L₁ L₂ : Subgroup G}
    (h₁ : IsWeakSBlock M (pCoreOf 2 H) L₁) (h₂ : IsWeakSBlock M (pCoreOf 2 H) L₂)
    (hne : barM M L₁ ≠ barM M L₂)
    (hk2 : ∀ L' : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L' →
      barM M L' = barM M L₁ ∨ barM M L' = barM M L₂)
    (hZ₁ : ¬ 3 ∣ Nat.card (barM M L₁ ⊓
      Subgroup.centralizer (barM M L₁ : Set (↥M ⧸ CFSG.pCore 2 ↥M)) : Subgroup _))
    (hZ₂ : ¬ 3 ∣ Nat.card (barM M L₂ ⊓
      Subgroup.centralizer (barM M L₂ : Set (↥M ⧸ CFSG.pCore 2 ↥M)) : Subgroup _)) : False := by
  have hLF' := CFSG.LocalAnalysis.RankThreeTheoremC.aschbacherLocalFactorization_proved
  have h85 : Asc81bEightFive := asc81bEightFive_of_factorization hLF'
  have h86 : Asc81bEightSix :=
    asc81bEightSix_of_bhs CFSG.LocalAnalysis.RankThreeTheoremC.bhsLocalCStar_proved
  have hX : NoXBlockFor G := hD2.noXBlockFor hctx.glob.toD1Global
  have hthree : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
      BlockHasThree M (pCoreOf 2 H) L := fun L hL =>
    hctx.pair.blockHasThree h85 h86 h93 hX kFactParabolicThree
      (citedBlockThreeTransvection_of_inverted hΛ) (kFactBlockThreeAltSeven_of_inverted hΛ) hL
  have hsolv : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
      BlockPLThreeSolv M (pCoreOf 2 H) L := fun L hL =>
    d2PairSolv G hctx.glob hctx.d1 P M A H R hctx.esc hctx.max hctx.beta hctx.pair hctx.strong
      hctx.perf L hL
  have hc₁ := pairBlockCensus hLF h418 hL27 h93 hD2 G P M A H R hctx L₁ h₁
  have hc₂ := pairBlockCensus hLF h418 hL27 h93 hD2 G P M A H R hctx L₂ h₂
  have hbad' := hbad G P M A H R hctx hev L₁ L₂ h₁ h₂ hne hk2 hZ₁ hZ₂
  have s₁ := shape_of_census hat hL32 hK3 hctx.pair.isKGroup.1 hctx.pair.asc81bHyp h₁
    (hctx.pair.nineThree_not_one h85 hX h₁).1 (hctx.pair.not_isSylowTwoOf_inf h85 hX h₁) hZ₁
    (hsolv L₁ h₁) hc₁ (hbad' L₁ (Set.mem_insert _ _))
  have s₂ := shape_of_census hat hL32 hK3 hctx.pair.isKGroup.1 hctx.pair.asc81bHyp h₂
    (hctx.pair.nineThree_not_one h85 hX h₂).1 (hctx.pair.not_isSylowTwoOf_inf h85 hX h₂) hZ₂
    (hsolv L₂ h₂) hc₂ (hbad' L₂ (Set.mem_insert_of_mem _ rfl))
  have hk2' : ∀ L' : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L' →
      barM M L' = barM M L₂ ∨ barM M L' = barM M L₁ := fun L' hL' => (hk2 L' hL').symm
  have hlow₁ : Open.pRank 3 L₂ ≤ 1 → Open.pRank 3 L₁ ≤ 2 → False := fun a b =>
    hlow G P M A H R hctx L₂ L₁ h₂ h₁ hne.symm hk2' hZ₂ hZ₁ a b
  have hlow₂ : Open.pRank 3 L₁ ≤ 1 → Open.pRank 3 L₂ ≤ 2 → False := fun a b =>
    hlow G P M A H R hctx L₁ L₂ h₁ h₂ hne hk2 hZ₁ hZ₂ a b
  by_cases hcf₁ : PairTwoAltSeven M L₁ ∨ IsA6OrU33 ↥(barM M L₁)
  · exact false_of_cf_block hCF hat hU33 hJ hnat hSA hctx h₁ h₂ hne hZ₁ hlow₁ hcf₁
  by_cases hcf₂ : PairTwoAltSeven M L₂ ∨ IsA6OrU33 ↥(barM M L₂)
  · exact false_of_cf_block hCF hat hU33 hJ hnat hSA hctx h₂ h₁ hne.symm hZ₂ hlow₂ hcf₂
  have t₁ : PairTwoEngineBlock M (pCoreOf 2 H) L₁ := by
    rcases s₁ with h | h | h
    · exact absurd (Or.inl h) hcf₁
    · exact absurd (Or.inr h) hcf₁
    · exact h
  have t₂ : PairTwoEngineBlock M (pCoreOf 2 H) L₂ := by
    rcases s₂ with h | h | h
    · exact absurd (Or.inl h) hcf₂
    · exact absurd (Or.inr h) hcf₂
    · exact h
  have h3₁ := three_dvd_card_barM h₁ hZ₁ (hthree L₁ h₁)
  have h3₂ := three_dvd_card_barM h₂ hZ₂ (hthree L₂ h₂)
  have hr₁ : 1 ≤ Open.pRank 3 L₁ := by
    rw [← pRank_barM_eq Nat.prime_three (by norm_num) M L₁ h₁.le]
    exact CFSG.AGLEmbeddingD2.one_le_pRank_of_dvd Nat.prime_three h3₁
  have hr₂ : 1 ≤ Open.pRank 3 L₂ := by
    rw [← pRank_barM_eq Nat.prime_three (by norm_num) M L₂ h₂.le]
    exact CFSG.AGLEmbeddingD2.one_le_pRank_of_dvd Nat.prime_three h3₂
  have hrank : 2 < Open.pRank 3 L₁ + Open.pRank 3 L₂ := by
    by_contra h
    push Not at h
    exact hlow₂ (by omega) (by omega)
  obtain ⟨d₁, d₂⟩ := doubling_of_engineBlocks hGN hCov hK hH29 hctx hev hX h₁ h₂ hne hk2 t₁ t₂
    hZ₁ hZ₂ h3₁ h3₂ hrank
  rcases isA6OrU33_or_rank_le_one hat hU33 hL32 h₁ hZ₁ d₁ with a₁ | b₁
  · exact hcf₁ (Or.inr a₁)
  rcases isA6OrU33_or_rank_le_one hat hU33 hL32 h₂ hZ₂ d₂ with a₂ | b₂
  · exact hcf₂ (Or.inr a₂)
  omega

end Final

theorem d2PairStrongThree_of_two_images (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (hΛ : KFactBlockInvertedThree) (hodd : PairOddIndexResidue) (hone : PairOneImagePureE)
    (hfix1 : PairOneImageFixE) (hcen : PairBlockCentreThree)
    (hLarge : LargeFieldParabolic) (h418 : Agl418) (hL27 : L2SevenRankOne)
    (hGN : GlaubermanNilesInput) (hCov : KFactParabolicCoverDoubling)
    (hK : KFactStrongThreeSolv) (hH29 : RankImageOne) (hCF : CitedFive) (hat : U33Atlas)
    (hU33 : U33Facts) (hJ : JordanPrimeCycle)
    (hnat : CFSG.HardMathSupport.Cooperstein.Coordinator.GF2EightFive) (hL32 : L32Atlas)
    (hSA : SmallRankAtlas) (hK3 : KFactNineThreeThreeBig) (hlow : ∀ (G : Type) [Group G] [Finite G]
        (P : Sylow 3 G) (M A H R : Subgroup G), PairStrongCtx P M A H R → ∀ L₁ L₂ : Subgroup G,
        IsWeakSBlock M (pCoreOf 2 H) L₁ → IsWeakSBlock M (pCoreOf 2 H) L₂ → barM M L₁ ≠ barM M L₂ →
        (∀ L' : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L' → barM M L' = barM M L₁ ∨ barM M L' =
        barM M L₂) → ¬ 3 ∣ Nat.card (barM M L₁ ⊓ Subgroup.centralizer (barM M L₁ : Set (↥M ⧸
        CFSG.pCore 2 ↥M)) : Subgroup _) → ¬ 3 ∣ Nat.card (barM M L₂ ⊓ Subgroup.centralizer (barM M
        L₂ : Set (↥M ⧸ CFSG.pCore 2 ↥M)) : Subgroup _) → Open.pRank 3 L₁ ≤ 1 → Open.pRank 3 L₂ ≤ 2 →
        False)
    (hbad : PairTwoBadShape2Residue) : D2PairStrongThree := by
  intro G _ _ hglob hD1 P M A H R hesc hmax hβ hpr hstr hperf
  have hctx : PairStrongCtx P M A H R := ⟨hglob, hD1, hesc, hmax, hβ, hpr, hstr, hperf⟩
  by_cases hev : PairEvenIndex M H
  swap
  · exact hodd G P M A H R hctx hev
  have hLF := CFSG.LocalAnalysis.RankThreeTheoremC.aschbacherLocalFactorization_proved
  have h84 : Asc81bEightFour := asc81bEightFour_of_factorization hLF
  have h85 : Asc81bEightFive := asc81bEightFive_of_factorization hLF
  have h86 : Asc81bEightSix :=
    asc81bEightSix_of_bhs CFSG.LocalAnalysis.RankThreeTheoremC.bhsLocalCStar_proved
  set S := pCoreOf 2 H
  have hX : NoXBlockFor G := hD2.noXBlockFor hglob.toD1Global
  have hH := hesc.pRank_H
  have hthree : ∀ L : Subgroup G, IsWeakSBlock M S L → BlockHasThree M S L := fun L hL =>
    hpr.blockHasThree h85 h86 h93 hX kFactParabolicThree
      (citedBlockThreeTransvection_of_inverted hΛ) (kFactBlockThreeAltSeven_of_inverted hΛ) hL
  have hy : ∀ L : Subgroup G, IsWeakSBlock M S L →
      ∃ y ∈ barM M (Subgroup.normalizer (S : Set G) ⊓ L), y ^ 3 = 1 ∧
        y ∉ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := fun L hL => by
    by_cases hZ : 3 ∣ Nat.card (barM M L ⊓
        Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) : Subgroup _)
    · exact hcen G P M A H R hctx L hL hZ
    · exact exists_order_three_noncentral hL.le (hthree L hL) hZ
  obtain ⟨L₁, hL₁⟩ := hpr.exists_weakSBlock h84 hX
  by_cases hk1 : ∀ L' : Subgroup G, IsWeakSBlock M S L' → barM M L' = barM M L₁
  ·
    obtain ⟨x, hxV, hx1, hrank⟩ := hone G P M A H R hctx hev L₁ hL₁ hk1
    exact hesc.false_of_pureVector hD1 hβ hstr hxV hx1 hrank
      (hfix1 G P M A H R hctx hev L₁ hL₁ hk1)
  ·
    simp only [not_forall] at hk1
    obtain ⟨L₂, hL₂, hne⟩ := hk1
    have hk2 : ∀ L' : Subgroup G, IsWeakSBlock M S L' →
        barM M L' = barM M L₁ ∨ barM M L' = barM M L₂ := by
      intro L' hL'
      by_contra hcon
      simp only [not_or] at hcon
      refine hpr.false_of_three_weakSBlock_images hH hthree ![L₁, L₂, L'] (fun i => ?_) ?_
      · fin_cases i
        · exact hL₁
        · exact hL₂
        · exact hL'
      · have h12 : barM M L₁ ≠ barM M L₂ := fun he => hne he.symm
        have h13 : barM M L₁ ≠ barM M L' := fun he => hcon.1 he.symm
        have h23 : barM M L₂ ≠ barM M L' := fun he => hcon.2 he.symm
        intro i j hij
        fin_cases i <;> fin_cases j <;> simp at hij ⊢
        all_goals first
          | exact absurd hij h12 | exact absurd hij.symm h12 | exact absurd hij h13
          | exact absurd hij.symm h13 | exact absurd hij h23 | exact absurd hij.symm h23
    have hne' : barM M L₁ ≠ barM M L₂ := fun he => hne he.symm
    have hk2' : ∀ L' : Subgroup G, IsWeakSBlock M S L' →
        barM M L' = barM M L₂ ∨ barM M L' = barM M L₁ := fun L' hL' => (hk2 L' hL').symm
    by_cases hZ₁ : 3 ∣ Nat.card (barM M L₁ ⊓
        Subgroup.centralizer (barM M L₁ : Set (↥M ⧸ CFSG.pCore 2 ↥M)) : Subgroup _)
    · exact hpr.false_of_two_weakSBlocks_of_center h84 h86 hX hH hL₁ hL₂ hne' hk2 hZ₁
        (hy L₁ hL₁) (hy L₂ hL₂)
    by_cases hZ₂ : 3 ∣ Nat.card (barM M L₂ ⊓
        Subgroup.centralizer (barM M L₂ : Set (↥M ⧸ CFSG.pCore 2 ↥M)) : Subgroup _)
    · exact hpr.false_of_two_weakSBlocks_of_center h84 h86 hX hH hL₂ hL₁ hne hk2' hZ₂
        (hy L₂ hL₂) (hy L₁ hL₁)
    exact (false_of_two_images h93 hD2 hΛ hLarge h418 hL27 hGN hCov hK hH29 hCF hat hU33 hJ hnat hL32
      hSA hK3 hlow hbad hctx hev hL₁ hL₂ hne' hk2 hZ₁ hZ₂).elim

end CFSG.AGLEmbeddingD2.McLaughlin
