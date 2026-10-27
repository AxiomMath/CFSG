module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKDL64I246Rest
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongKFSeitz
public import CFSG.LieType.SeitzGeneration.SeitzStatus

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding CFSG.Blueprint Subgroup
open scoped MatrixGroups

@[expose] def KDL64I246Co1Case : Prop :=
  ∀ (Z : Type) [Group Z] [Finite Z], CatalogSimpleSections Z →
    primeComplementCore (G := Z) 5 = ⊥ →
    ∀ L : Subgroup Z, IsComponentOf L ⊤ → NativeSporadic.IsSporadic (↥L ⧸ center ↥L) .Co1 →
      ∀ P : Subgroup Z, P ≤ L → IsPGroup 5 P → ¬ 5 ∣ (P.subgroupOf L).index →
        3 ≤ Open.pRank 5 P →
        ∀ Y : Subgroup Z,
          (∀ S : Subgroup Z, S ≤ P → 2 ≤ Open.pRank 5 S → normalizer (S : Set Z) ≤ Y) →
          (∀ E : Subgroup Z, E ≤ P → IsElemAbelian 5 E → Nat.card E = 5 ^ 3 →
            ∀ S : Subgroup Z, S ≤ E → 1 ≤ Open.pRank 5 S → normalizer (S : Set Z) ≤ Y) →
          L ≤ Y

theorem kdL64I246Rest_of_co1
    (hCo1 : KDL64I246Co1Case) :
    KDL64I246Rest := by
  intro p hp hp5 Z _ _ hcat hpc L hL hcases P hPL hPp hPidx hrk Y hY2 hY1
  have hLq : Open.IsQuasisimple ↥L := hL.2.2
  have hQ := GL83.CompFam.quasisimple_quotient_nonabelian hLq
  haveI : IsSimpleGroup (↥L ⧸ center ↥L) := hLq.2
  rcases hcases with ⟨K, _, _, hpK, ⟨e⟩⟩ | ⟨q, K, _, _, hKq, hq, ⟨e⟩⟩ | ⟨rfl, hCo⟩
  · obtain ⟨d, ⟨eQ⟩, hpd, hexc⟩ := FongKF.lieIndex_of_statedPSL hp hp5 K hpK e
    exact FongKF.le_of_seitzGen hp L P Y hLq hPL hPp hPidx hrk
      (FongKF.seitzGen_of_lie CFSG.LieType.SeitzGeneration.kFactSeitzRankTwo_holds hp (by omega)
        d hpd hexc hQ eQ) hY2 hY1
  · obtain ⟨d, ⟨eQ⟩, hpd, hexc⟩ := FongKF.lieIndex_of_statedPSU hp hp5 q K hKq hq e
    exact FongKF.le_of_seitzGen hp L P Y hLq hPL hPp hPidx hrk
      (FongKF.seitzGen_of_lie CFSG.LieType.SeitzGeneration.kFactSeitzRankTwo_holds hp (by omega)
        d hpd hexc hQ eQ) hY2 hY1
  · exact hCo1 Z hcat hpc L hL hCo P hPL hPp hPidx hrk Y hY2 hY1

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
