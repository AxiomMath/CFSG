module

public import CFSG.CGT.PushingUpLit.CGT6.SixFourTail5
public import CFSG.CGT.PushingUpLit.CGT6.SixFourU3Model

public section

namespace CFSG.CGT.PushingUpLit.CGT6

section U3

theorem slTailU3 (hS : CFSG.CGT.Timmesfeld75.SimpleCaseListStmt)
    (h215 : CFSG.CGT.Timmesfeld75.Lemma215Stmt) (hL : CFSG.CGT.Timmesfeld75.ListWCIdentification) :
    SLTailU3 :=
  slTailU3_of hS h215 hL u3Frame

end U3

section Certified

theorem aschbacherSixFourCore_of_hyps (hS : CFSG.CGT.Timmesfeld75.SimpleCaseListStmt)
    (h215 : CFSG.CGT.Timmesfeld75.Lemma215Stmt) (hL : CFSG.CGT.Timmesfeld75.ListWCIdentification) :
    AschbacherSixFourCore :=
  aschbacherSixFourCore_of_u3 hS h215 hL (slTailU3 hS h215 hL)

end Certified

end CFSG.CGT.PushingUpLit.CGT6
