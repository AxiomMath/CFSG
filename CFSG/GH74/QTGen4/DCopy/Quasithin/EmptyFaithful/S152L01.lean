module

public import CFSG.Quasithin.EmptyFaithful.S152L01
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.S152Stmts

public section

namespace CFSG.Quasithin

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

theorem stageLemma15201_of_F4 (h157 : StageLemma1517) (h1515 : StageTheorem15115_F4) :
    StageLemma15201_F4 := by
  intro G _ _ T Mc M hs
  exact lemma_15_2_1 (h157 G T Mc M hs.qtfe hs.mf hs.ce) (h1515 G T Mc M hs.qtfe hs.mf hs.ce)

end CFSG.Quasithin
