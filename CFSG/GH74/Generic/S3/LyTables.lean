module

public import CFSG.GH74.Generic.S3.LyFinal
public import CFSG.GH74.GLS.TwoThin.G.Final

public section

namespace CFSG.GH74.Generic.S3

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.GH74.GLS.TwoThin CFSG.GH74.E2

theorem b_S3_LyJNT_of_tables
    (hG : GenericKnownFacts) (hF : E2ComponentFacts)
    (hU33 : TwoThinU33Centralizers) (h2M : TwoThinC2VerticalG_2M12) (hSL2 : LyVertB2SL2) :
    B_S3_LyJNT :=
  b_S3_LyJNT_of_sl2 hG
    (twoThinKGroupFactQ_of_coreP (fun _ _ _ hH L => gen4Comp_of_gen4Cen hH L)
      (twoThinKGroupCoreGC_of_tables hG hF hU33 h2M)).1 hSL2

end CFSG.GH74.Generic.S3
