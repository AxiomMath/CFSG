module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeData
public meta import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeData

public section

namespace CFSG.EvenSporadicStandard.Co3Std.CentT

open CFSG.EvenSmallLie.OmegaEight CFSG.Monster.B.Co2.Native

@[expose] def o8OuterCentArr (i : ℕ) : ℕ → Array ℕ
  | 0 => idA 360
  | k + 1 => omegaW ((cent0Words.getD i []).getD k [])

@[expose] def o8OuterCentCheck (_ : Unit := ()) : Bool :=
  [3, 4].all fun i => (List.range 5).all fun a => (List.range a).all fun b =>
    !eqA 360 (o8OuterCentArr i a) (o8OuterCentArr i b)

end CFSG.EvenSporadicStandard.Co3Std.CentT
