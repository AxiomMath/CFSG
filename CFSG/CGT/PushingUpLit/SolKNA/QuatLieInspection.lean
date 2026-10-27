module

public import CFSG.CGT.PushingUpLit.SolKNA.QuatLieFinal
public import CFSG.CGT.PushingUpLit.SolKNA.QuatLieNeg

public section

namespace CFSG.CGT.PushingUpLit.SolKNA

open CFSG.ClassicalInvolution.Q3


theorem quaternionInspectionLie_of_cit3 (h1 : CIT3Inductive) (h2 : TightLiftSimple) :
    QuaternionInspectionLie :=
  quaternionInspectionLie_of_cit3_neg neg3Table_holds h1 h2

end CFSG.CGT.PushingUpLit.SolKNA
