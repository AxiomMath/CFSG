module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevRadicalSimple
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113OverSmall
import CFSG.GroupTheory.SylowIntersectionControl.GomiChevRadicalOfChar

public section

namespace CFSG.GroupTheory

open CFSG.Open CFSG.QuasithinUnique.Bridge.Over

theorem chevParabolicRadicalSimple_of_psu_three_three
    {K : Type} [Group K] [Finite K] (hK : IsSimpleGroup K)
    (h : StatedClassicalModel K .PSU 3 3 1) : ChevParabolicRadicalSimple K :=
  chevParabolicRadicalSimple_of_overgroups hK (overgroups_psu_three_three h)

end CFSG.GroupTheory
