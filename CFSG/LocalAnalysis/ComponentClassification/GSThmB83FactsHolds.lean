module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB83Q3Step4c
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB83S2Final
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog8Small
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog8SecInner
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallQ3
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallQ3Conf
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallA6
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4Sec8
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4F2
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4Sec8L2Inv
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4Layer
public import Certificates.Certificate43
public import Certificates.Certificate2006
public import Certificates.Certificate2007
public import Certificates.Certificate2008
public import Certificates.Certificate2009
public import Certificates.Certificate2012
public import Certificates.Certificate2013
public import Certificates.Certificate2014
public import Certificates.Certificate2015
public import Certificates.Certificate5108
public import CFSG.LieType.Universal.SpinOmega.Range
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsCentModel

public section

namespace CFSG.ComponentClassification.GSThmB

namespace Cat8

theorem q3Facts :
    Q3Facts :=
  ⟨cfSec8Simple, cfSec8InnerCentralizer, CatFactsSmall.cfQ3Out, CatFactsSmall.cfQ3L0,
    CatFactsSmall.cfQ3F2, CatFactsSmall.cfQ3Conf, CatFactsSmall.cfA6Diag,
    CatFactsSmall.cfA6SylowCent, CatFactsSmall.cfA6NoComm, CatFactsSmall.cfA6InnerInv,
    CatFactsSmall.cfQ3NoNilp⟩

theorem s2Facts :
    S2Facts :=
  ⟨CatFactsSp4.cfSec8JOrder, CatFactsSp4.cfSp4F2, CatFactsSp4.cfL2Inv, CatFactsSp4.cfSp4Layer,
    CatFactsSp4.cfSec8Order⟩

end Cat8

end CFSG.ComponentClassification.GSThmB
