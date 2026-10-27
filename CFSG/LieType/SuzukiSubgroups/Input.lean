module

public import CFSG.LieType.SuzukiSubgroups.Main
public import CFSG.LocalAnalysis.WeakClosure81.TwelveInputs

public section

namespace CFSG.LieType.SuzukiSubgroups

theorem suzukiSubgroupInput_holds :
    CFSG.LocalAnalysis.WeakClosure81.SuzukiSubgroupInput :=
  fun _ _ _ _ hH _ hU ⟨_, hEU, hE, hE4⟩ => le_normalizer_or_isSz hH hU hEU hE hE4

end CFSG.LieType.SuzukiSubgroups
