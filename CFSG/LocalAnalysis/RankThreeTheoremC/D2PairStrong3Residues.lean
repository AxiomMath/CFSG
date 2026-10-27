module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D2PairStrong3Irr
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2Reduction

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.QuasithinUnique
open CFSG.RankThreeCoreUniqueness.Helpers

@[expose] def D2PairA6Residue3 (G : Type) [Group G] [Finite G] : Prop :=
  Setting G → TheoremD1 G → ∀ M : Subgroup G, rankThreeIsMaxTwoLocal M → D2FullCoreAt G M →
    D2ThreeClauseAt G M → ∀ (P : Sylow 3 G) (A H R : Subgroup G), 3 ∈ rankThreeSigmaA G →
    IsCoreMaxLocal 3 P M → D2Escape 3 P M A H R → D2EscapeMax 3 P M R → AGLPair 3 M H R →
    rankThreeGamma 1 3 (P : Subgroup G) ≤ M → D2PerfectThreePrime H M →
    IsElemAbelian 3 R → Nat.card R = 9 →
    IrreducibleOn (H ⊓ M ⊓ Subgroup.normalizer (R : Set G)) R →
    ¬ TransitiveOnNonidentity (H ⊓ M ⊓ Subgroup.normalizer (R : Set G)) R →
    ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
      (∀ L' : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L' → barM M L' = barM M L) →
      3 ≤ Open.pRank 3 L →
      barM M R ≤ barM M L ⊔ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) →
      barM M R ⊓ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) = ⊥ → False

variable {G : Type} [Group G] [Finite G]

theorem blockPLThreeSolv_of_perfectThreePrime {M H R : Subgroup G} (hpair : AGLPair 3 M H R)
    (hperf : D2PerfectThreePrime H M) {L : Subgroup G}
    (hL : IsWeakSBlock M (pCoreOf 2 H) L) : BlockPLThreeSolv M (pCoreOf 2 H) L :=
  hpair.blockPLThreeSolv_of_perfectThreePrime hperf hL

end CFSG.LocalAnalysis.RankThreeTheoremC
