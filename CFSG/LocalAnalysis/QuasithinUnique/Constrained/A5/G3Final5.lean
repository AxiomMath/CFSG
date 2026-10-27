module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3Final4
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3J4N3Done
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.MainNative
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1J4OutFinal
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.ThreeCoverFinal
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A3Native39
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporSchreier

public section

namespace CFSG.QuasithinUnique.A5.G3

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native

theorem a314A5Excluded_proved
    : A314A5Excluded :=
  have h36 := a36CoreForSQTKCat_proved
  have h37 := a37ForSQTKCat_proved
  have h38 := a38ForSQTKCat_of_facts CFSG.Quasithin.mult2Fact a134SQTKFactCat h36 h37
  have h39 := a39ForSQTKCat_of_facts
    (schreierFactListCat_of_J4 (sporadicSchreierCase_J4_of_outOdd Setup.X1.j4OuterOdd)) h36 h37 h38
  a314A5Excluded_direct8 threeCoverFactCat h36 h37 h39 j4Normalizer3

end CFSG.QuasithinUnique.A5.G3
