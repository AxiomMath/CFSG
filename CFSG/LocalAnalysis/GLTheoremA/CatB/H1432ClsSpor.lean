module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1432SporD4
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1432SporG2

public section


namespace CFSG.LocalAnalysis.GLTheoremA.H1420.ClsRed

theorem i1432ClsD4_of_lie
    (hLie : I1432ClsD4Lie) : I1432ClsD4 :=
  i1432ClsD4_of_parts CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds
    SporD4.i1432SporD4S_holds hLie

theorem i1432ClsG2_of_lie
    (hLie : I1432ClsG2Lie) : I1432ClsG2 :=
  i1432ClsG2_of_parts CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds
    SporG2.i1432SporG2S_holds hLie

end CFSG.LocalAnalysis.GLTheoremA.H1420.ClsRed

end
