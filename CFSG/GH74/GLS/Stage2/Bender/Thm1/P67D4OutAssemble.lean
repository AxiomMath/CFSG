module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4OutStage
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4OutG2

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

theorem d4OuterThree_of_leaves (hA2 : D4OuterThreeA2Toral) (hEll : D4OuterThreeEll)
    (hMinus : D4OuterThreeMinus) : D4OuterThree :=
  d4OuterThree_of_stages d4OuterThreeG2_thm hA2 hEll hMinus

end CFSG.GH74.GLS.Stage2.Bender.Thm1
