module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113DichNat
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42J2Main
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42HSMain
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42RuMain
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1J4OutFinal
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42ThreeA7Final

public section

namespace CFSG.QuasithinUnique.Bridge

theorem asB42DichotomyNat_proved
    : AsB42DichotomyNat :=
  asB42DichotomyNat_of_exclusions J2Excl.sporadicExclusion_J2
    Setup.X1.sporadicExclusion_J4_proved HSExcl.sporadicExclusion_HS
    RuExcl.sporadicExclusion_Ru threeA7Exclusion

end CFSG.QuasithinUnique.Bridge
