module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeCharData
public meta import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeCharData

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.Steinberg

@[noinline, expose] def e6NonInnerCheck (_ : Unit := ()) : Bool :=
  e6ThreeStabs.all fun S =>
    decide (triPairing (vec3 (τ := .E6) S.vec) e6Omega3 = 0) ||
      (S.passing e6Certificate).all fun t => t == List.range Tag.E6.rank

end CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3

end
