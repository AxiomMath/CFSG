module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4MainD
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4UnMain

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.GH74.GLS.Stage2.OddAut
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87 CFSG.GH74.GLS.IVK.Proofs2.Ivk47

theorem cf67D4_thm_of_a2Minus_thm (hleaf : G2D4InnerPlaneGen) : CF67D4 :=
  cf67D4_thm_of_a2Minus hleaf d4OuterThreeA2Minus_thm

end CFSG.GH74.GLS.Stage2.Bender.Thm1
