module

public import CFSG.CGT.PushingUpLit.CGT6.SixFourTail3
public import CFSG.CGT.PushingUpLit.CGT6.SixFourA9Center

public section

namespace CFSG.CGT.PushingUpLit.CGT6

theorem slTailA9_of (hS : CFSG.CGT.Timmesfeld75.SimpleCaseListStmt)
    (h215 : CFSG.CGT.Timmesfeld75.Lemma215Stmt) (hL : CFSG.CGT.Timmesfeld75.ListWCIdentification) :
    SLTailA9 := by
  intro G _ _ _ _ Y T R _ hctx n hn hnat hA
  exact eight_sl_not_alt9 a9Center hctx hn hnat hS h215 hL hA

theorem aschbacherSLTail'_of_parts' (hS : CFSG.CGT.Timmesfeld75.SimpleCaseListStmt)
    (h215 : CFSG.CGT.Timmesfeld75.Lemma215Stmt) (hL : CFSG.CGT.Timmesfeld75.ListWCIdentification)
    (hU3 : SLTailU3) (hA67 : SLTailA67) : AschbacherSLTail' :=
  aschbacherSLTail'_of_parts hS h215 hL hU3 (slTailA9_of hS h215 hL) hA67

section Certified


theorem aschbacherSixFourCore_of_parts' (hS : CFSG.CGT.Timmesfeld75.SimpleCaseListStmt)
    (h215 : CFSG.CGT.Timmesfeld75.Lemma215Stmt) (hL : CFSG.CGT.Timmesfeld75.ListWCIdentification)
    (hU3 : SLTailU3) (hA67 : SLTailA67) : AschbacherSixFourCore :=
  aschbacherSixFourCore_of_tail' hS h215 hL (aschbacherSLTail'_of_parts' hS h215 hL hU3 hA67)

end Certified

end CFSG.CGT.PushingUpLit.CGT6
