module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D2PairStrong3Residues

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.QuasithinUnique
open CFSG.RankThreeCoreUniqueness.Helpers

@[expose] def D2PairA6Residue3U (G : Type) [Group G] [Finite G] : Prop :=
  Setting G → TheoremD1 G → ∀ M : Subgroup G, rankThreeIsMaxTwoLocal M → D2FullCoreAt G M →
    D2ThreeClauseAt G M → ∀ (P : Sylow 3 G) (A H R : Subgroup G), 3 ∈ rankThreeSigmaA G →
    IsCoreMaxLocal 3 P M → D2Escape 3 P M A H R → AGLPair 3 M H R →
    rankThreeGamma 1 3 (P : Subgroup G) ≤ M → D2PerfectThreePrime H M →
    IsElemAbelian 3 R → Nat.card R = 9 →
    IrreducibleOn (H ⊓ M ⊓ Subgroup.normalizer (R : Set G)) R →
    ¬ TransitiveOnNonidentity (H ⊓ M ⊓ Subgroup.normalizer (R : Set G)) R →
    ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
      (∀ L' : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L' → barM M L' = barM M L) →
      3 ≤ Open.pRank 3 L →
      barM M R ≤ barM M L ⊔ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) →
      barM M R ⊓ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) = ⊥ → False

theorem D2PairA6Residue3U.toOld {G : Type} [Group G] [Finite G] (h : D2PairA6Residue3U G) :
    D2PairA6Residue3 G :=
  fun hS hD1 M hM ha hb P A H R hp hMP hesc _ hpr hstr hperf hRel hR9 hirr htrans L hL hk1 hr3
      hRL hker =>
    h hS hD1 M hM ha hb P A H R hp hMP hesc hpr hstr hperf hRel hR9 hirr htrans L hL hk1 hr3 hRL
      hker

end CFSG.LocalAnalysis.RankThreeTheoremC
