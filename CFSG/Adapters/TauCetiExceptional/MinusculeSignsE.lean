module

public import CFSG.Adapters.TauCetiExceptional.MinusculeAdjSigns

public section

namespace CFSG.TauCetiBridge.Minuscule

open CFSG.LieType.Steinberg.Minuscule

@[expose] def e6Signs : AdjSigns .E6 where
  eps := [false, true, true, false, true, false]
  sgn := [
    true, false, false, true, false, true, false, true, true, false, true, false, false, true,
    true, false, false, false, true, true, false, false, true, false, false, true, true, true,
    true, true, false, false, false, false, false, false, true, false, false, true, true, true,
    true, false, false, true, true, true, true, true, false, false, false, false, false, true,
    true, true, false, true, true, true, true, false, false, false, true, true, true, false, true,
    true]

@[expose] def e7Signs : AdjSigns .E7 where
  eps := [false, true, true, false, true, false, true]
  sgn := [
    true, false, false, true, false, true, false, false, true, true, false, true, false, false,
    true, true, false, false, true, true, false, true, true, false, false, true, false, false,
    true, true, false, false, true, true, true, false, false, false, false, false, false, true,
    true, false, false, false, true, true, true, true, false, false, false, true, false, false,
    true, true, true, true, true, false, false, false, false, false, false, false, false, false,
    true, true, true, true, true, false, false, true, true, true, true, true, true, false, false,
    false, false, false, false, true, true, true, true, false, true, true, true, true, true, true,
    false, false, false, false, true, true, true, true, true, true, true, true, false, false,
    true, true, true, true, true, false, true, true, true, false, true, true]

theorem e6Signs_check : e6Signs.check e6Data = true := by
  decide +kernel

theorem e7Signs_check : e7Signs.check e7Data = true := by
  decide +kernel

end CFSG.TauCetiBridge.Minuscule
