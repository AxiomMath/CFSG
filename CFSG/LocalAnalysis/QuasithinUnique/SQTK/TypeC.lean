module

public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeA
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeCCarrier

public section

namespace CFSG.QuasithinUnique.SQTK

open CFSG.Open.SQTKTauCeti TauCeti CFSG.Assembly.LowTwoRank

theorem tcLieCase_C (r : ℕ) (q : PrimePower) (hv : (LieTypeIndex.C r q).Valid) :
    TCLieCase ⟨.C r q, hv⟩ := by
  intro G _ _ _ _ hSQT ⟨e⟩
  exact sqtkSimpleList_of_statedClassicalModel hSQT (statedClassicalModel_typeC r q hv e)

end CFSG.QuasithinUnique.SQTK
