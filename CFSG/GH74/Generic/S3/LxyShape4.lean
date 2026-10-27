module

public import CFSG.GH74.Generic.S3.LxyShape3
public import CFSG.GH74.GLS.TwoThin.G.Final

public section

namespace CFSG.GH74.Generic.S3

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.GH74.GLS.TwoThin CFSG.GH74.E2

theorem b_S3_LxyShapeJNT_of_tables
    (hG : GenericKnownFacts) (hF : E2ComponentFacts)
    (hU33 : TwoThinU33Centralizers) (h2M : TwoThinC2VerticalG_2M12) (hB2 : B2NoncentralTable) :
    B_S3_LxyShapeJNT :=
  b_S3_LxyShapeJNT_of_parts hG
    (twoThinKGroupFactQ_of_coreP (fun _ _ _ hH L => gen4Comp_of_gen4Cen hH L)
      (twoThinKGroupCoreGC_of_tables hG hF hU33 h2M)).1 hB2

end CFSG.GH74.Generic.S3
