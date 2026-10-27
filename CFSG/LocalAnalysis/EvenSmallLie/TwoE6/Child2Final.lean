module

public import CFSG.LocalAnalysis.EvenSmallLie.TwoE6.Stroth23InnerMain
public import CFSG.LocalAnalysis.EvenSmallLie.TwoE6.CoverUniqueFinal
public import CFSG.LocalAnalysis.EvenSmallLie.TwoE6.OddSquare

public section


namespace CFSG.EvenSmallLie.TwoE6

theorem stroth23 : Stroth23 :=
  stroth23_of_inputs doubleCoverUnique coverOuterLeTwo stroth22 Stroth23Inner.stroth23Inner

theorem child2E6 : Child2E6 :=
  child2E6_of_stroth stroth21 stroth23

end CFSG.EvenSmallLie.TwoE6
