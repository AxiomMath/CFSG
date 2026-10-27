module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B113K.DetFF
public import CFSG.Adapters.CatalogAgree

public section

namespace CFSG.Quasithin.B113KDet

theorem catalogBridge_holds :
    CatalogBridge :=
  fun S _ h => CFSG.Open.QTFaithfulEmptyTauCeti.inCatalog_of_catalog S h

end CFSG.Quasithin.B113KDet
