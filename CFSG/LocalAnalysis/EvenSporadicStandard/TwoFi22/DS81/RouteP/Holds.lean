module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.HoldsOfPins
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Pins.Assemble

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP

theorem fi24RecognitionLocal_holds :
    Fi24RecognitionLocal :=
  fi24RecognitionLocal_of_pins_holds (fun h hr => Std.nonempty_pins h hr)

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP
