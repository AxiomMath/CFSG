module

public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeC
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2Carrier

public section

namespace CFSG.QuasithinUnique.SQTK

open CFSG.Open.SQTKTauCeti TauCeti CFSG.Assembly.LowTwoRank

theorem tcLieCase_B2 (q : PrimePower) (hv : (LieTypeIndex.B 2 q).Valid) :
    TCLieCase ⟨.B 2 q, hv⟩ := by
  intro G _ _ _ _ hSQT ⟨e⟩
  exact sqtkSimpleList_of_statedClassicalModel hSQT (statedClassicalModel_typeB2 q hv e)

theorem tcLieCase_of_isTypeCorB2 {d : ValidLieTypeIndex} (hd : IsTypeCorB2 d) : TCLieCase d := by
  obtain ⟨d, hv⟩ := d
  cases d with
  | B r q =>
    have hr : r = 2 := hd
    subst hr
    exact tcLieCase_B2 q hv
  | C r q => exact tcLieCase_C r q hv
  | _ => exact hd.elim

end CFSG.QuasithinUnique.SQTK
