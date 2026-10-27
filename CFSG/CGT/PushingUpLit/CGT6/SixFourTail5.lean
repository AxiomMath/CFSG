module

public import CFSG.CGT.PushingUpLit.CGT6.SixFourTail4
public import CFSG.CGT.PushingUpLit.CGT6.SixFourA67

public section

namespace CFSG.CGT.PushingUpLit.CGT6

theorem slTailA67_of (hS : CFSG.CGT.Timmesfeld75.SimpleCaseListStmt)
    (h215 : CFSG.CGT.Timmesfeld75.Lemma215Stmt) (hL : CFSG.CGT.Timmesfeld75.ListWCIdentification) :
    SLTailA67 := by
  intro G _ _ _ _ Y T R _ hctx n hn hnat hA U₀ hU hU₀T hYU hYs
  exact (eight_sl_not_alt67 hctx hn hnat hS h215 hL hA hU hU₀T hYU hYs).elim

section Certified

theorem aschbacherSixFourCore_of_u3 (hS : CFSG.CGT.Timmesfeld75.SimpleCaseListStmt)
    (h215 : CFSG.CGT.Timmesfeld75.Lemma215Stmt) (hL : CFSG.CGT.Timmesfeld75.ListWCIdentification)
    (hU3 : SLTailU3) : AschbacherSixFourCore :=
  aschbacherSixFourCore_of_parts' hS h215 hL hU3 (slTailA67_of hS h215 hL)

end Certified

end CFSG.CGT.PushingUpLit.CGT6
