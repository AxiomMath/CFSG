module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K518YCover
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K518Res
import CFSG.LocalAnalysis.AGLEmbedding.BlockFactReductionsII
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K518YCent
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K518YLie
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K518YOuter

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbeddingD2.GN

theorem k518Y_of_cover
    (hcov : ∀ (X : Type) [Group X] [Finite X] (T T₁ T₂ : Subgroup X), GNSetting X T →
      GNGood T T₁ T₂ → GNCoverP T T₁ T₂)
    (hG : KFactChevGenThree) (hO : KFact518Out) : K518Y := by
  intro X _ _ T T₁ T₂ hX hg p hp hp2 Ls _ hLs _ hinv m1 m2 n1 n2 _ hoth hn
  have hc := hcov X T T₁ T₂ hX hg
  have hK := not_dvd_card_centralizer_of_cover hg.centre hc hp hp2 hLs hinv m1 m2 n1 n2 hoth hn
  refine pElementSubgroup_le_comap_of_sup hp hK fun g hgp => ?_
  by_contra hgn
  obtain ⟨x, hxp, hxT, hxn⟩ := exists_pElement_not_mem_sup_of_cover hc hp hp2 hLs.1 hn hgp hgn
  apply hxn
  rcases (hg.shape Ls hLs).2 with ⟨hcl, hr⟩ | ⟨n, hn', ⟨e⟩⟩
  · exact mem_sup_centralizer_of_classical hG hO hX hg hp hp2 hLs hinv m1 m2 n1 n2 hn hcl hr
      hxp hxT
  · have hN : toStar T x ∈ Subgroup.normalizer (Ls : Set (X ⧸ gnC T)) := by
      haveI := hn
      rw [Subgroup.normalizer_eq_top]
      exact Subgroup.mem_top _
    obtain ⟨k, hk⟩ := hxp
    refine CFSG.AGLEmbedding.mem_sup_centralizer_of_not_dvd_card_outer (k := k) hp ?_ hN ?_
    · rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv]
      exact CFSG.AGLEmbedding.not_dvd_card_outer_alternatingGroup n
        (by rcases hn' with h7 | ⟨h8, -⟩ <;> omega) p hp hp2
    · rw [← map_pow, ← hk, pow_orderOf_eq_one, map_one]

end CFSG.LocalAnalysis.RankThreeUC.S15
