module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InClauses5
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InClauses3
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InClauses4

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin

theorem lemma2_4_8
    (E : Lemma248Inputs) : Lemma2_4_8 := by
  intro G _ _ T M H S L D n h
  have dat := E.data h
  exact ⟨dat.clause1 h, dat.clause2 h, dat.clause3 h, dat.clause4 h, dat.exists_B h,
    fun B hB => dat.clause6 h hB, dat.clause7 h, Lin2Data.clause8 h, dat.clause9 h⟩

end CFSG.QuasithinUnique.Lin2
