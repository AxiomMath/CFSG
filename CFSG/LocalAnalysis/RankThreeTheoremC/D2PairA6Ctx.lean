module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.ParabolicCover
import CFSG.LocalAnalysis.RankThreeUC.StronglyEmbedded
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2Ambient3
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2PairStrong3Irr

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.QuasithinUnique
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

structure PairCtx3 {G : Type} [Group G] [Finite G] (P : Sylow 3 G) (M A H R : Subgroup G) :
    Prop where
  setting : Setting G
  d1 : TheoremD1 G
  maxLocal : rankThreeIsMaxTwoLocal M
  fullCore : D2FullCoreAt G M
  threeClause : D2ThreeClauseAt G M
  sigma : 3 ∈ rankThreeSigmaA G
  core : IsCoreMaxLocal 3 P M
  esc : D2Escape 3 P M A H R
  pair : AGLPair 3 M H R
  gamma : rankThreeGamma 1 3 (P : Subgroup G) ≤ M
  perf : D2PerfectThreePrime H M

variable {G : Type} [Group G] [Finite G] {P : Sylow 3 G} {M A H R : Subgroup G}

theorem PairCtx3.strong (h : PairCtx3 P M A H R) : GLBStronglyEmbedded 3 M := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have := h.setting.simple
  obtain ⟨hPM, hP3⟩ := sylow_le_of_isCoreMaxLocal h.setting h.sigma h.core
  have hMtop : M ≠ ⊤ :=
    CFSG.PreuniquenessRankFour.Helpers.twoLocal_ne_top h.setting.nonab h.maxLocal.1
  have hP1 : (P : Subgroup G) ≠ ⊥ := by
    intro h0
    obtain ⟨E, hE, -, hcard⟩ := CFSG.PreuniquenessRankFour.Helpers.pRank_attained 3
      Nat.prime_three (P : Subgroup G)
    rw [h0, le_bot_iff] at hE
    rw [hE, Subgroup.card_bot, hP3] at hcard
    norm_num at hcard
  have hstr := (CFSG.LocalAnalysis.RankThreeUC.gamma_one_le_iff_isStronglyPEmbedded hPM hMtop
    hP1).mp h.gamma
  exact ⟨hstr.1, hstr.2.1, fun g hg hdvd =>
    hstr.2.2 g⁻¹ (fun h' => hg (by simpa using M.inv_mem h')) hdvd⟩

theorem PairCtx3.d1At (h : PairCtx3 P M A H R) : D1At G 3 :=
  d1At_of_theoremD1 h.d1 h.sigma

@[expose] def PairOneImageLieTR3 (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (P : Sylow 3 G) (M A H R : Subgroup G), PairCtx3 P M A H R → 2 ∣ (H ⊓ M).relIndex H →
    ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
    (∀ L' : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L' → barM M L' = barM M L) →
    NineThreeTwo M (pCoreOf 2 H) L → 3 ≤ Open.pRank 3 L →
    ¬ 3 ∣ Nat.card (barM M L ⊓
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) : Subgroup _) →
    IsOneImageList (↥(barM M L) ⧸ Subgroup.center ↥(barM M L))

@[expose] def PairBlockType3 (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (P : Sylow 3 G) (M A H R : Subgroup G), PairCtx3 P M A H R →
    ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L → 3 ≤ Open.pRank 3 L →
    ¬ 3 ∣ Nat.card (barM M L ⊓
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) : Subgroup _) →
    NineThreeTwo M (pCoreOf 2 H) L

@[expose] def KFactBlockOneImageIrr3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M S L : Subgroup G), Open.IsKGroup ↥M → Asc81bHyp M S →
    IsWeakSBlock M S L → NineThreeTwo M S L → BlockPLThreeSolv M S L → Open.pRank 3 M ≤ 3 →
    IsOneImageList (↥(barM M L) ⧸ Subgroup.center ↥(barM M L)) →
    ∀ E : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), IsElemAbelian 3 E → Nat.card E = 9 →
      E ≤ barM M (Subgroup.normalizer (S : Set G) ⊓ L) →
      (∀ T : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M),
        T ≤ barM M (Subgroup.normalizer (S : Set G) ⊓ L) → IsPGroup 3 T → Nat.card T ≤ 9) →
      ¬ IrreducibleOn
        (Subgroup.normalizer (E : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ⊓
          Subgroup.normalizer
            (barM M (Subgroup.normalizer (S : Set G) ⊓ L) : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ⊓
          Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))) E

end CFSG.LocalAnalysis.RankThreeTheoremC
