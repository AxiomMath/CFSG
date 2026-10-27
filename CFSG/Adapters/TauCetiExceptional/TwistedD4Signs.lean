module

public import CFSG.Adapters.TauCetiExceptional.TwistedD4Data
public import CFSG.Adapters.TauCetiExceptional.MinusculeAdjSigns
public import CFSG.Adapters.TauCetiExceptional.MinusculeMatch

public section

namespace CFSG.TauCetiBridge.Twisted

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Minuscule CFSG.TauCetiBridge.Minuscule

@[expose] def d4tSigns : AdjSigns .D4 where
  eps := [false, false, true, false]
  sgn := [true, true, false, true, false, true, false, true, true, false, false, true, true, true,
    true, true, false, false, false, true, false, true, true, false]

theorem d4tSigns_check : d4tSigns.check d4tData = true := by decide +kernel

end CFSG.TauCetiBridge.Twisted
