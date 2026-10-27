module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.PairSepAssembly
import CFSG.LocalAnalysis.AGLEmbedding.AscEightFive
import CFSG.LocalAnalysis.AGLEmbedding.AscEightFour
import CFSG.LocalAnalysis.AGLEmbedding.AscEightSix
import CFSG.LocalAnalysis.RankThreeTheoremC.D2PairRes3Single
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.PermJordan
public import CFSG.LocalAnalysis.AGLEmbeddingD2.PairBlocks
public import CFSG.LocalAnalysis.AGLEmbeddingD2.PairPureAssembly
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2LocalCGT3

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbedding CFSG.AGLEmbeddingD2
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

@[expose] def KFactBlockCentrePLRank : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M S L : Subgroup G), IsWeakSBlock M S L →
    NineThreeConclusion M S L → ¬ NineThreeOne L →
    (NineThreeTwo M S L → ¬ IsSylowTwoOf (barM M (S ⊓ L)) (barM M L)) → BlockPLThreeSolv M S L →
    barM M L ⊓ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ≤
      barM M (Subgroup.normalizer (S : Set G) ⊓ L) →
    3 ∣ Nat.card (barM M L ⊓
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) : Subgroup _) →
    ¬ 9 ∣ Nat.card (barM M L ⊓
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) : Subgroup _) ∧
      2 ≤ Open.pRank 3 (barM M (Subgroup.normalizer (S : Set G) ⊓ L))


open CFSG.LocalAnalysis.RankThreeTheoremC in
theorem centre_le_blockPL (hD2 : D1NoXBlock) {G : Type} [Group G] [Finite G] {P : Sylow 3 G}
    {M A H R : Subgroup G} (hctx : PairStrongCtx P M A H R) {L : Subgroup G}
    (hL : IsWeakSBlock M (pCoreOf 2 H) L) :
    barM M L ⊓ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ≤
      barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L) := by
  have hfact := CFSG.LocalAnalysis.RankThreeTheoremC.aschbacherLocalFactorization_proved
  have h84 : Asc81bEightFour := asc81bEightFour_of_factorization hfact
  have h86 : Asc81bEightSix :=
    asc81bEightSix_of_bhs CFSG.LocalAnalysis.RankThreeTheoremC.bhsLocalCStar_proved
  have hX : NoXBlockFor G := hD2.noXBlockFor hctx.glob.toD1Global
  rintro z ⟨hzL, hzC⟩
  have hzB : z ∈ barM M (Subgroup.normalizer (pCoreOf 2 H : Set G)) :=
    hctx.pair.mem_barM_normalizer_of_centralizes_weakSBlocks h84 h86 hX fun L' hL' => by
      by_cases hbar : barM M L = barM M L'
      · rw [← hbar]
        exact hzC
      · have hc := CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _
          hL.component hL'.component hbar
        have := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc
        exact this hzL
  exact hctx.pair.barM_inf_barM_le ⟨hzL, hzB⟩

theorem pairBlockCentreThree_of_cited (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (hK : KFactBlockCentrePLRank) : PairBlockCentreThree := by
  intro G _ _ P M A H R hctx L hL hZ
  have hfact := CFSG.LocalAnalysis.RankThreeTheoremC.aschbacherLocalFactorization_proved
  have h85 : Asc81bEightFive := asc81bEightFive_of_factorization hfact
  have hX : NoXBlockFor G := hD2.noXBlockFor hctx.glob.toD1Global
  have hnot := hctx.pair.nineThree_not_one h85 hX hL
  have hconc := hctx.pair.nineThree h93 hL
  have hsolv := d2PairSolv G hctx.glob hctx.d1 P M A H R hctx.esc hctx.max hctx.beta hctx.pair
    hctx.strong hctx.perf L hL
  obtain ⟨h9, hr⟩ := hK G M (pCoreOf 2 H) L hL hconc hnot.1 hnot.2 hsolv
    (centre_le_blockPL hD2 hctx hL) hZ
  obtain ⟨E, hEP, hE, hEcard⟩ := CFSG.PreuniquenessRankFour.Helpers.pRank_attained 3
    Nat.prime_three (barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L))
  by_contra hcon
  push Not at hcon
  have hEC : E ≤ barM M L ⊓
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := fun e he =>
    ⟨barM_mono inf_le_right (hEP he), hcon e (hEP he) (hE.2 e he)⟩
  apply h9
  have hdvd := Subgroup.card_dvd_of_le hEC
  rw [hEcard] at hdvd
  have h32 : (3 : ℕ) ^ 2 ∣
      3 ^ Open.pRank 3 (barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L)) :=
    pow_dvd_pow 3 hr
  simpa using h32.trans hdvd

end CFSG.AGLEmbeddingD2.McLaughlin
