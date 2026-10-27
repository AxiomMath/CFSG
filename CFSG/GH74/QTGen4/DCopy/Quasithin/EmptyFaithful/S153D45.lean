module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.S153D35
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.S153D43

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

theorem stageComponentCase_of_blocks_F4 (h113 : StageLemma14113) (h2 : StageComponentTwo_F4)
    (h1 : StageComponentOne_F4) : StageComponentCase_F4 := by
  intro G _ _ T Mc M V₁ V₂ Yp t h I hI hmin hnc
  have hle := h.pRank_Yp_le_two h113
  have hge := h.one_le_pRank_Yp h113 hI
  rcases (by omega : CFSG.Open.pRank 3 Yp = 1 ∨ CFSG.Open.pRank 3 Yp = 2) with h1' | h2'
  · exact h1 G T Mc M V₁ V₂ Yp t h h1' I hI hmin hnc
  · exact h2 G T Mc M V₁ V₂ Yp t h h2' I hI hmin hnc

end CFSG.Quasithin
