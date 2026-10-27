module

public import CFSG.GH74.GLS.TwoThin.G.Cover
public import CFSG.GH74.GLS.TwoThin.G.C2Vertical

public section

namespace CFSG.GH74.GLS.TwoThin

open CFSG.GH74 CFSG.GH74.Generic CFSG.GH74.E2

theorem twoThinKGroupCoreGC_of_tables
    (hG : GenericKnownFacts) (hF : E2ComponentFacts)
    (hU33 : TwoThinU33Centralizers) (h2M : TwoThinC2VerticalG_2M12) : TwoThinKGroupCoreGC :=
  ⟨twoThinC2VerticalGC hG hF hU33 h2M, twoThinT2VerticalP _, twoThinC2CoverGC hG hF⟩

theorem s_twoThinOfB2G_of_tables
    (hG : GenericKnownFacts) (hF : E2ComponentFacts)
    (hU33 : TwoThinU33Centralizers) (h2M : TwoThinC2VerticalG_2M12) : S_twoThinOfB2G :=
  s_twoThinOfB2G_of_coreGC (twoThinKGroupCoreGC_of_tables hG hF hU33 h2M)

end CFSG.GH74.GLS.TwoThin
