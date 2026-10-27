module

public import CFSG.GH74.Generic.S3.LxyShape4
public import CFSG.GH74.Generic.S3.B2Tab3

public section

namespace CFSG.GH74.Generic.S3

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.GH74.GLS.TwoThin CFSG.GH74.E2

theorem b_S3_LxyShapeJNT_proved
    (hG : GenericKnownFacts) (hF : E2ComponentFacts)
    (hU33 : TwoThinU33Centralizers) (h2M : TwoThinC2VerticalG_2M12) :
    B_S3_LxyShapeJNT :=
  b_S3_LxyShapeJNT_of_tables hG hF hU33 h2M b2NoncentralTable_proved

end CFSG.GH74.Generic.S3
