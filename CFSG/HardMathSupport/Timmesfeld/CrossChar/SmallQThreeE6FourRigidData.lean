module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeE6FourData

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3

open CFSG.Blueprint.Chevalley Timmesfeld.Co1Leaf
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1T

namespace Native

@[noinline, expose] def e6AntiCheck (_ : Unit := ()) : Bool :=
  let kb := (stdBasis 5).map (liftL (τ := .E6) e6InnerVec)
  let B := gramL .E6
  let E := simpleL .E6
  (tuplesL B (fibRoots (rootsN .E6) kb) E (E.map fun e => fibL kb (e.map fun x => -x))
    (E.map fun e => formB B e e)).all fun t => !e6WeylTest t

@[noinline, expose] def e6FourRigidCheck (_ : Unit := ()) : Bool :=
  e6AntiCheck () && kerNonemptyOK .E6

end Native

end CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3

end
