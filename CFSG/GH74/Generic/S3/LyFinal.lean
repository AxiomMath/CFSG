module

public import CFSG.GH74.Generic.S3.LyVertMain

public section

namespace CFSG.GH74.Generic.S3

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.GH74.GLS.TwoThin

theorem b_S3_LyJNT_of_sl2
    (hF : GenericKnownFacts)
    (hKG : TwoThinKGroupVerticalQ Gen4Cen) (hSL2 : LyVertB2SL2) : B_S3_LyJNT :=
  b_S3_LyJNT_of_parts hF hKG (lyNotDiag_proved hF) (lyVertTrivial_of_sl2 hSL2)

end CFSG.GH74.Generic.S3
