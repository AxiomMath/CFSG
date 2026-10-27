module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoCo1.HypOneInputs

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1.InvNative
  CFSG.Sporadic.Co1.TwoBNative CFSG.Sporadic.Co1Block CFSG.Sporadic.Co1Block.Native
  CFSG.EvenSporadicStandard.TwoCo1.HypOne

@[expose] def twoBCommWX : List Int := [4, -3, -4, -3, 1, 2, 1, 3, -4, -1, -3, -1, -2]

@[expose] def twoBCommWY : List Int := [-4, -3, -2, 1, 3, 1, 3, -4, -1, -3, -1]

@[expose] def twoBCommOf (D₃ : List Rows × List Rows × Bool) : Bool :=
  D₃.2.2 && (mul (D₃.1.getD 4 one) aR == mul aR (D₃.1.getD 4 one)) &&
    (mul (D₃.1.getD 5 one) aR == mul aR (D₃.1.getD 5 one)) &&
    (mul (D₃.1.getD 4 one) (D₃.1.getD 5 one) == mul aR (mul (D₃.1.getD 5 one) (D₃.1.getD 4 one)))

@[noinline, expose] def twoBCommCheck : Bool :=
  (brayRows aR twoBD1).2.2 && (dag (brayElts (brayRows aR twoBD1) twoBBray) sylD2B).2.2 &&
    twoBCommOf (dag (pickRows (dag (brayElts (brayRows aR twoBD1) twoBBray) sylD2B) sylIdxB)
      [twoBCommWX, twoBCommWY])

end CFSG.EvenSporadicStandard.Solomon78
