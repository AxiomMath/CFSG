module

public import CFSG.GH74.GLS.LU.Local.L3InvLin
public import CFSG.GH74.GLS.LU.Local.L3InvUni
public import CFSG.GH74.GLS.LU.Local.L3Facts

public section

namespace CFSG.GH74.GLS.LU.Local

theorem l3InvTorus : L3InvTorus := by
  intro J _ _ δ q hδ hq hq5 hJ a b ha hb hab hcomm
  rcases hδ with rfl | rfl
  · exact l3InvTorus_lin J q hq hq5 hJ a b ha hb hab hcomm
  · exact l3InvTorus_uni J q hq hq5 hJ a b ha hb hab hcomm

end CFSG.GH74.GLS.LU.Local
