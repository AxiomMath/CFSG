module

public import CFSG.Fischer.Classification.Recognition.Main
public import CFSG.Fischer.Classification.Recognition.CaseSym
public import CFSG.Fischer.Classification.Recognition.CaseSp
public import CFSG.Fischer.Classification.Recognition.CaseO
public import CFSG.Fischer.Classification.Recognition.CaseU
public import CFSG.Fischer.Classification.Recognition.CaseR3

public section

namespace CFSG.Fischer.Classification.Recognition

open CFSG.Open

theorem classicalComponentOrders : ClassicalComponentOrders := by
  intro G _ _ D hH hc d hd K hK
  rcases hc with h1 | h2 | h3 | h4 | h5
  · exact componentOrder_case1 h1 hd hK
  · exact componentOrder_case2 hH h2 hd hK
  · exact componentOrder_case3 h3 hd hK
  · exact componentOrder_case4 hH h4 hd hK
  · exact componentOrder_case5 hH h5 hd hK

end CFSG.Fischer.Classification.Recognition
