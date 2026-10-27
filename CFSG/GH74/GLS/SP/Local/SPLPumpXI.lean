module

public import CFSG.GH74.GLS.SP.Local.SPLPumpXH
public import CFSG.GH74.GLS.SP.Local.SPLUniqInv
public import CFSG.GH74.GLS.SP.Local.SPLAltCover
public import CFSG.GH74.GLS.SP.Local.SPLDiag

public section

namespace CFSG.GH74.GLS.SP.Local

theorem splPumpX_proved
    (hG : CFSG.GH74.Generic.GenericKnownFacts) (hF : CFSG.GH74.E2.E2ComponentFacts) : SPLPumpX :=
  splPumpX_of_shapes hG hF stableUniqueInvolution stableDoubleCoverAlt stableL34Cover
    otherUniqueInvolution diagonalImpossible

end CFSG.GH74.GLS.SP.Local
