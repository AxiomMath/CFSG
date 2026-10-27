module

public import CFSG.GF2Type.Smith1979W3.SuzL34Holds
public import CFSG.GF2Type.Smith1979W3.Cert690.Census.Sound

public section

namespace CFSG.GF2Type.Smith1979W3

section Certs

theorem smith1979WidthThreeCharTwoKP_holds : Smith1979WidthThreeCharTwoKP :=
  smith1979WidthThreeCharTwoKP_of_cert690 Cert690.censusPlusProp_holds
    Cert690.censusMinusProp_holds Cert690.pglFactsProp_holds Cert690.pglSquareProp_holds
    Cert690.a8SquareProp_holds

end Certs

end CFSG.GF2Type.Smith1979W3
