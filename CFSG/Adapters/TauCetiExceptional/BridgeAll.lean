module

public import CFSG.Adapters.TauCetiExceptional.BridgeF4
public import CFSG.Adapters.TauCetiExceptional.BridgeE8
public import CFSG.Adapters.TauCetiExceptional.BridgeG2
public import CFSG.Adapters.TauCetiExceptional.MinusculeBridgeE
public import CFSG.Adapters.TauCetiExceptional.TwistedD4Push
public import CFSG.Adapters.TauCetiExceptional.TwistedE6Push
public import CFSG.Adapters.TauCetiExceptional.FrameworkReduction

public section

namespace CFSG.TauCetiBridge

theorem chevalleyBridges :
    ChevalleyBridges where
  g2 := untwistedBridge_G2
  f4 := untwistedBridge_F4
  e6 := untwistedBridge_E6
  e7 := untwistedBridge_E7
  e8 := untwistedBridge_E8
  twistedE6 := Twisted.twistedBridge_twistedE6
  trialityD4 := Twisted.twistedBridge_trialityD4

end CFSG.TauCetiBridge
