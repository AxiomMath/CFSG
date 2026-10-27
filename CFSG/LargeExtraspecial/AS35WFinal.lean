module

public import CFSG.LargeExtraspecial.AS35WM12
public import CFSG.LargeExtraspecial.AS35WJ2
public import CFSG.LargeExtraspecial.AS35WSp4Gen
public import CFSG.LargeExtraspecial.AS35WA8
public import CFSG.LargeExtraspecial.AS35WL43
public import CFSG.LargeExtraspecial.AS35WU4

public section

namespace CFSG.LargeExtraspecial

open AS35W

namespace S14

theorem aschbacherWidthTwoResidual_of_gh74
    (hGH : GH74Models) (hR2 : RankTwoW2Input) : AschbacherWidthTwoResidual :=
  aschbacherWidthTwoResidual_of_inspection hGH hR2
    (gh74W2Input_of sp4W2Input l4W2Input u4W2Input l5W2Input u5W2Input
      w2Good_alternating_eight m12W2Input j2W2Input)

end S14

end CFSG.LargeExtraspecial
