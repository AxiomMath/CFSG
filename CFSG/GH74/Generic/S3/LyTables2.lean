module

public import CFSG.GH74.Generic.S3.LyTables
public import CFSG.GH74.Generic.S3.LyB2Main

public section

namespace CFSG.GH74.Generic.S3

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.GH74.GLS.TwoThin CFSG.GH74.E2

theorem b_S3_LyJNT_proved
    (hG : GenericKnownFacts) (hF : E2ComponentFacts)
    (hU33 : TwoThinU33Centralizers) (h2M : TwoThinC2VerticalG_2M12) : B_S3_LyJNT :=
  b_S3_LyJNT_of_tables hG hF hU33 h2M
    (lyVertB2SL2_proved hG
      (twoThinKGroupFactQ_of_coreP (fun _ _ _ hH L => gen4Comp_of_gen4Cen hH L)
        (twoThinKGroupCoreGC_of_tables hG hF hU33 h2M)))

end CFSG.GH74.Generic.S3
