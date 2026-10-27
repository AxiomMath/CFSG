module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.S152Stmts
public import CFSG.Quasithin.EmptyFaithful.S151Basic
public import CFSG.Quasithin.EmptyFaithful.S152L16

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

theorem stageLemma15216_of_F4 (h14 : StageLemma15214_F4) (h13 : StageLemma15213_F4)
    (h11 : StageLemma15211_F4) (hN : StageNotation15209_F4) : StageLemma15216_F4 := by
  intro G _ _ T Mc M hs H hH B₀ hB₀ I hI
  exact lemma_15_2_16 hs.qtfe hB₀ hI (h14 G T Mc M hs B₀ hB₀) (h13 G T Mc M hs H hH)
    (h11 G T Mc M hs H hH) (hN G T Mc M hs H hH)

theorem stageLemma15217_of_F4 (h14 : StageLemma15214_F4) (h16 : StageLemma15216_F4) :
    StageLemma15217_F4 := by
  intro G _ _ T Mc M hs B₀ hB₀ I hI
  obtain ⟨H, hH⟩ := exists_isHStar hs.qtfe.inM_mc hs.mf.1.1 hs.mf.2.1.symm
  exact lemma_15_2_17 (h14 G T Mc M hs B₀ hB₀) (h16 G T Mc M hs H hH B₀ hB₀ I hI)

end CFSG.Quasithin
