module

public import CFSG.Quasithin.EmptyFaithful.S152U18
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.S152Stmts

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

theorem stageLemma15218_of_F4 (h5 : StageLemma15205_F4) (h159 : StageLemma1519)
    (h11 : StageLemma15211_F4) (h13 : StageLemma15213_F4) (h14 : StageLemma15214_F4)
    (hN : StageNotation15209_F4) (h16 : StageLemma15216_F4) (h17 : StageLemma15217_F4)
    (hOm : Om4FactsStatement) : StageLemma15218_F4 := by
  intro G _ _ T Mc M hs H hH B₀ hB₀ I hI
  exact lemma_15_2_18 hs hH hB₀ hI
    ⟨h5 G T Mc M hs, h159 G T Mc M hs.qtfe hs.mf hs.ce, h13 G T Mc M hs H hH,
      h14 G T Mc M hs B₀ hB₀, h11 G T Mc M hs H hH, hN G T Mc M hs H hH,
      h16 G T Mc M hs H hH B₀ hB₀ I hI, h17 G T Mc M hs B₀ hB₀ I hI⟩ hOm

end CFSG.Quasithin
