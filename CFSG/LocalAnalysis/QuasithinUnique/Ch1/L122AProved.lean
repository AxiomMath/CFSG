module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L122AMain
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A3Native36
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A3Native38
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A134Final
public import CFSG.Quasithin.Background.KnownMultTypes

public section

namespace CFSG.QuasithinUnique.Vol2Native

theorem lemma122A_proved
    : Lemma122A :=
  have h36 := a36CoreForSQTKCat_proved
  have h37 := a37ForSQTKCat_proved
  lemma122A_of_inputs h37 (a38ForSQTKCat_of_facts CFSG.Quasithin.mult2Fact a134SQTKFactCat h36 h37)

end CFSG.QuasithinUnique.Vol2Native
