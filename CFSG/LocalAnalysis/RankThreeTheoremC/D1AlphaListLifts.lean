module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1AlphaListE3
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1AlphaListLiftsSpor
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1AlphaListLiftsG2
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1AlphaListLiftsU43

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open TauCeti

theorem kFactLiftU43 : KFactLiftU43 := fun q hv hq => U43Lift.hasLiftableTriple_U43 q hv hq

theorem kFactLiftG23 :
    KFactLiftG23 :=
  fun q hv hq => G2Lift.hasLiftableTriple_G2 q hv hq

theorem kFactLiftJ3 :
    KFactLiftJ3 :=
  hasLiftableTriple_J3

theorem kFactLiftMcL :
    KFactLiftMcL :=
  hasLiftableTriple_McL

theorem kFactAlphaLifts :
    KFactAlphaLifts :=
  ⟨kFactLiftU43, kFactLiftG23, kFactLiftJ3, kFactLiftMcL⟩

end CFSG.LocalAnalysis.RankThreeTheoremC
