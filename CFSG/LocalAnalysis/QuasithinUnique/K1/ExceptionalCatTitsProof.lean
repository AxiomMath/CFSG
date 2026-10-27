module

public import CFSG.LocalAnalysis.QuasithinUnique.K1.ExceptionalCatTits
public import CFSG.Sporadic.Schreier.TitsQTModel
public import CFSG.Sporadic.Schreier.TitsQTInner

public section

namespace CFSG.QuasithinUnique.K1

theorem titsNoStronglyClosedElemAbelian
    : TitsNoStronglyClosedElemAbelian :=
  fun X _ _ h => CFSG.Sporadic.Schreier.TitsQT.tits_model_noStronglyClosedElemAbelian X h

theorem titsSylowCentralizingAutInner
    : TitsSylowCentralizingAutInner :=
  fun X _ _ h => CFSG.Sporadic.Schreier.TitsQT.tits_model_sylowCentralizingAutInner X h

end CFSG.QuasithinUnique.K1
