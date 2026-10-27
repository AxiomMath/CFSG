module

public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeA
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti

public section

namespace CFSG.QuasithinUnique.SQTK

open CFSG.Open.SQTKTauCeti TauCeti CFSG.Assembly.LowTwoRank

theorem tcLieCase_twistedA (r : ℕ) (q : PrimePower) (hv : (LieTypeIndex.twistedA r q).Valid) :
    TCLieCase ⟨.twistedA r q, hv⟩ := by
  intro G _ _ _ _ hSQT ⟨e⟩
  exact sqtkSimpleList_of_statedClassicalModel hSQT (statedClassicalModel_twistedA r q hv e)

theorem tcLieCase_of_isTwistedA {d : ValidLieTypeIndex} (hd : IsTwistedA d) : TCLieCase d := by
  obtain ⟨d, hv⟩ := d
  cases d with
  | twistedA r q => exact tcLieCase_twistedA r q hv
  | _ => exact hd.elim

end CFSG.QuasithinUnique.SQTK
