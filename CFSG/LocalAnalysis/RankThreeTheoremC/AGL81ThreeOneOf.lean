module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeOneCentralizer
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeOneLieChar
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeOneLieCross
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeOneRankTwo
public import CFSG.LocalAnalysis.GL83PartI.I_24_3.IsoPlaneMain

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111.ThreeOne

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers

section ReductionsCert


variable {p : ℕ} {G : Type} [Group G] [Finite G] {K : Subgroup G} {P : Sylow p G}
  {E : Subgroup G}

theorem Hyp.center_eq_bot_of_three (H : Hyp p K P E) (h3 : 3 ≤ Open.pRank p (P : Subgroup G))
    (hnot : ¬ K ≤ GLBWeakCore p (P : Subgroup G)) : Subgroup.center K = ⊥ := by
  have hO := GL83.I243.gl83ComponentPCoreTrivial_holds G H.catalog p P K H.prime H.ne_two h3
    H.isComponentOf hnot
  have hle : Subgroup.center K ≤ CFSG.pCore p K := le_sSup ⟨inferInstance, H.isPGroup_center⟩
  rw [hO] at hle
  exact le_bot_iff.1 hle

end ReductionsCert

section AssemblyCert


variable {p : ℕ} {G : Type} [Group G] [Finite G] {K : Subgroup G} {P : Sylow p G}
  {E : Subgroup G}

theorem Hyp.threeOne_of_three
    (H : Hyp p K P E) (h3 : 3 ≤ Open.pRank p (P : Subgroup G))
    (hnot : ¬ K ≤ GLBWeakCore p (P : Subgroup G)) :
    OnThreeOneList p K ∧ Subgroup.center K = ⊥ := by
  have hZ := H.center_eq_bot_of_three h3 hnot
  refine ⟨?_, hZ⟩
  by_cases hC : Subgroup.centralizer (K : Set G) = ⊥
  · obtain ⟨i, ⟨e⟩⟩ := (H.isCatalogGroup hZ).2.2
    cases i with
    | cyclic q hq => exact (H.false_of_cyclic e).elim
    | alternating n hn => exact H.threeOne_alt h3 hnot hC n hn e
    | lie d =>
      by_cases hpd : p = d.1.characteristic
      · exact H.threeOne_lieChar h3 hnot hC d hpd e
      · exact H.threeOne_lieCross h3 hnot hC d hpd e
    | sporadic s => exact H.threeOne_spor h3 hnot hC s e
  · exact H.threeOne_of_centralizer_ne_bot h3 hnot hZ hC

theorem kFactThreeOne_of_sporPlane
    (hS : KFactThreeOneSporPlane) : KFactThreeOne := by
  refine kFactThreeOne_of_hyp fun p G _ _ K P E H hnot => ?_
  by_cases h3 : 3 ≤ Open.pRank p (P : Subgroup G)
  · rw [if_pos h3] at hnot
    exact H.threeOne_of_three h3 hnot
  · rw [if_neg h3] at hnot
    exact H.threeOne_of_two hS h3 hnot

end AssemblyCert

end CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111.ThreeOne
