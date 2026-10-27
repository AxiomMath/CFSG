module

public import CFSG.GF2Type.Smith1979W3.Cert690.Census.Base
public import Certificates.Certificate690004
public import Certificates.Certificate690005
public import Certificates.Certificate690006

public section

namespace CFSG.GF2Type.Smith1979W3.Cert690

theorem censusPlusProp_holds :
    CensusPlusProp :=
  censusPlus_sound_of Certificates.certificate690004.1 Certificates.certificate690005

theorem censusMinusProp_holds :
    CensusMinusProp :=
  censusMinus_sound_of Certificates.certificate690004.2 Certificates.certificate690006

end CFSG.GF2Type.Smith1979W3.Cert690

end
