module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ChainT0Data

public section

namespace CFSG.EvenSmallLie.OmegaEight.Chain

open CFSG.EvenSmallLie.UnitarySix.YamadaPar Stage1

@[expose] def commCheck : Bool :=
  let T := mulTab .plus
  let LT := liftTab
  (List.range 64).all fun q => [false, true].all fun e => (List.range 64).all fun s =>
    let l := tmul T LT (dig4 641, false, 0) (twoV q, e, s)
    let r := tmul T LT (twoV q, e, s) (dig4 641, false, 0)
    l == r || l == tmul T LT r (twoV 1, false, 0)

end CFSG.EvenSmallLie.OmegaEight.Chain
