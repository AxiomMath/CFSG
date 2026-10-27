module

public import CFSG.Sporadic.J4.QTNative

public section

namespace CFSG.EvenSporadicStandard.J4Std.DataMod

open CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT

@[expose] def liftWordS : List Int := [-2, -3, 1, 3, -1, 2, -1, -1, -2, -2, 1, -2, 3]

@[expose] def liftWordT : List Int :=
  [-3, -3, -2, -3, 1, -2, 1, 3, -1, -3, 2, -1, -2, -3, -3, 1, 3, 1, 1, 1, 2, 2, 3, -2, -3, -1, -1,
    -3, 1, 3, 1, -3, -2, -2, -3, -3, -1, -1, -1, -3]

@[expose] def liftMaskS : Nat := 29

@[expose] def liftMaskT : Nat := 154

@[expose] def liftRows (loc inv : Array (Array V2)) (w : List Int) (c : Nat) : Array V2 :=
  mulRows (wordRows loc inv w) (etaRows (uTab loc inv) 11 c)

@[expose] def chkLift (loc inv : Array (Array V2)) : Bool :=
  let S := liftRows loc inv liftWordS liftMaskS
  let T := liftRows loc inv liftWordT liftMaskT
  eqRows (mulRows S S) idRows && eqRows (mulRows T T) idRows &&
    eqRows (mulRows (mulRows S T) (mulRows S T)) idRows

end CFSG.EvenSporadicStandard.J4Std.DataMod
