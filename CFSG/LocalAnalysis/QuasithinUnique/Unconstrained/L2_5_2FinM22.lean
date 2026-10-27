module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2FinM2Tab
public import CFSG.Sporadic.Mathieu.M22
public meta import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2FinM2Tab
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2FinM22Inputs
public import Certificates.Certificate4065
public import Certificates.Certificate3029
public meta import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2
public meta import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2
public meta import Certificates.Certificate113
public import Certificates.Certificate113

public section

namespace CFSG.QuasithinUnique.Unc25G2

namespace M2x

open CFSG.Sporadic.Mathieu CFSG.Blueprint

set_option synthInstance.maxSize 32768 in
set_option synthInstance.maxHeartbeats 400000 in
theorem check22 : Check 22 d22 :=
  Certificates.certificate4065

theorem twoE_M22 : TwoE NativeSporadic.M22 :=
  twoE_of_check NativeSporadic.M22 (a := m22gA) (b := m22gB) m22a.2 m22b.2 d22 (by decide)
    (by decide) card_M22 check22

end M2x

end CFSG.QuasithinUnique.Unc25G2
