module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.ModelAutXCheck
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.ModelAutXData

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81

@[expose] def axCertificate : Bool :=
  axCheck axMs axQs axFam && axWordsOK axGc axQs axWs axMs

end CFSG.EvenSporadicStandard.TwoFi22.DS81
