module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23GOCList
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7Out

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.GOC

section Main


theorem goldOutCyc : CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.GoldOutCyc := by
  intro X _ _ hs hty Q hQ
  exact isCyclic_map_fstar_of_goldschmidtSimpleType hty hQ

end Main

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.GOC
