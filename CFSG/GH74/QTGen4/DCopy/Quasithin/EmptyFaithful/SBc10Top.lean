module

public import CFSG.Quasithin.EmptyFaithful.SBc10Top
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.S153H31

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace SBc10


theorem input15331_of_msOutcome_F4 (h113 : StageLemma14113) (hMS : Input31MSOutcome_F4) : Input15331_F4 :=
  S153H.input15331_of_named_inputs_F4 hMS
    (SBc4.input31CentQ_of_cover (SBc8.input31Cover_of_short h113
      (SBc9.input31CoverShort_of_g2 h113 (SBc9.input31CoverG2_of_noFixed (input31G2NoFixed_holds h113)))))
    (SBc7.input31NotCentQ_of_residue (SBc8.input31QleYp_of_short h113
      (SBc9.input31QleYpShort_of_g2 h113 (SBc9.input31QleYpG2_of_cover (input31G2Cover_holds h113)))))

end SBc10

end CFSG.Quasithin
