module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4Dec2A
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4Dec2B0
public import CFSG.Sporadic.J4.QT2LocScanCheck
public import Certificates.Certificate4029

public section

namespace CFSG.QuasithinUnique.A5

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT2

theorem j4_hdA
    : ∀ V' ∈ reps2A, ClassRad V' ∨ NoNonHBlockAt Hj V' :=
  j4_hdA_of_X0 Certificates.certificate4029.basic centralizer_fiveElt_eq_X0Sub.le

theorem j4_hdB0
    : ∀ V' ∈ reps2B0, ClassRad V' ∨ NoNonHBlockAt Hj V' :=
  j4_hdB0_of_X0 Certificates.certificate4029.basic centralizer_fiveElt_eq_X0Sub.le

end CFSG.QuasithinUnique.A5
