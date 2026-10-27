module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.L34Three
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2Reduction

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2
open CFSG.RankThreeCoreUniqueness.Helpers (primeComplementCore)
open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

@[expose] def D2L34BetaResidue3 (G : Type) [Group G] [Finite G] : Prop :=
  Setting G → TheoremD1 G → ∀ M : Subgroup G, rankThreeIsMaxTwoLocal M → D2FullCoreAt G M →
    D2ThreeClauseAt G M → ∀ (P : Sylow 3 G) (A H R : Subgroup G), 3 ∈ rankThreeSigmaA G →
    IsCoreMaxLocal 3 P M → D2Escape 3 P M A H R → D2EscapeMax 3 P M R →
    ∀ d : TauCeti.ValidLieTypeIndex, IsL34Index d →
    ∀ (Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3))
      (K : Subgroup (H ⧸ primeComplementCore (G := H) 3)),
      (Rbar : Subgroup _) = (R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore 3)) →
      D2AlmostSimple 3 (H ⧸ primeComplementCore (G := H) 3) Rbar
        ((A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore 3)))
        (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore 3))) K →
      Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group) →
      (A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore 3)) ≤ K →
      ¬ Subgroup.centralizer
          (((A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore 3)) : Subgroup _) :
            Set (H ⧸ primeComplementCore (G := H) 3)) ≤
        (A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore 3)) →
      pCoreOf 2 (H ⊓ M) ≠ pCoreOf 2 H →
      Subgroup.normalizer (pCoreOf 2 (H ⊓ M) : Set G) = H ⊓ M →
      (∃ C : Subgroup G, C ≤ pCoreOf 2 (H ⊓ M) ∧ C ≠ ⊥ ∧
        (C.subgroupOf (pCoreOf 2 (H ⊓ M))).Characteristic ∧
          H ≤ Subgroup.normalizer (C : Set G)) →
      False

end CFSG.LocalAnalysis.RankThreeTheoremC
