module

public import CFSG.LocalAnalysis.RankThreeUC.GN15AltBlockW
public import CFSG.LocalAnalysis.RankThreeUC.GN15AltModPow

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbeddingD2.GN
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.RankThree.PartTwo
open scoped commutatorElement

theorem gnBlockLift_holds : GNBlockLift := by
  intro X _ _ T hX L hL _ n hn9 hodd _ hlayer H Kb hQH hblk _ hC hKL
  obtain ⟨g, W, π, hg, hWV, -, hWK, hπk, hπi, hVW⟩ := hlayer
  have hKb : Kb ≤ gnPre T L := fun x hx => hKL (Subgroup.mem_map_of_mem _ hx)
  have hWne : ⁅W, gnPre T L⁆ ≠ ⊥ := by
    intro hbot
    apply hC
    rw [← hVW] at hbot
    have h1 : gnV T ≤ Subgroup.centralizer (gnPre T L : Set X) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.1 hbot
    exact hKb.trans (Subgroup.le_centralizer_iff.1 h1)
  exact false_of_block_of_naturalOn hX hL hn9 hodd g hg W hWV hWK π hπk hπi hWne hQH hblk hC hKL

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15
