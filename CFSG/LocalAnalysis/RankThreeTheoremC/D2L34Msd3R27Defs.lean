module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.QuasithinUnique
open CFSG.RankThreeCoreUniqueness.Helpers (primeComplementCore)

@[expose] def D2L34NonExtremalL34 (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (d : TauCeti.ValidLieTypeIndex) (P : Sylow 3 G) (M A H R : Subgroup G)
    (Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) 3)),
    D2L34SideCtx3 G d P M A H R Rbar K → Group.IsSolvable M → Nat.card R = 27 →
    ∀ T : Subgroup G, IsSylowTwoOf T (H ⊓ M) →
    ∀ E N : Subgroup G, D2Escape 3 P M E N E → Subgroup.normalizer (T : Set G) ≤ N →
    ∀ (Ebar : Sylow 3 (N ⧸ primeComplementCore (G := N) 3))
      (K' : Subgroup (N ⧸ primeComplementCore (G := N) 3)),
      (Ebar : Subgroup _) = (E.subgroupOf N).map (QuotientGroup.mk' (primeComplementCore 3)) →
      D2AlmostSimple 3 (N ⧸ primeComplementCore (G := N) 3) Ebar
        ((E.subgroupOf N).map (QuotientGroup.mk' (primeComplementCore 3)))
        (((N ⊓ M).subgroupOf N).map (QuotientGroup.mk' (primeComplementCore 3))) K' →
      ∃ d' : TauCeti.ValidLieTypeIndex, IsL34Index d' ∧
        Nonempty (K' ≃* (TauCeti.CFSGIndex.lie d').Group)

end CFSG.LocalAnalysis.RankThreeTheoremC
