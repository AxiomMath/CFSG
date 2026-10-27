module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.LyCheck

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic

open CFSG.Sporadic.Ly.Native CFSG.Sporadic.He.Native CFSG.Sporadic.LySchreier.Native

set_option compiler.extract_closed false

@[expose] def ly31Word : List Int := [1, 2, 2, 2]

@[expose] def ly31WordInv : List Int := [-2, -2, -2, -1]

@[expose] def ly31C (_ : Unit := ()) : Mat := lySeedWordM ly31Word

@[expose] def ly31Ci (_ : Unit := ()) : Mat := lySeedWordM ly31WordInv

@[expose] def ly31P (_ : Unit := ()) : Mat :=
  mulM 5 111 matA (mulM 5 111 (mulM 5 111 (ly31C ()) matA) (ly31Ci ()))

@[expose] def ly31Check (_ : Unit := ()) : Bool :=
  mulM 5 111 (ly31C ()) (ly31Ci ()) == idM 111 && powM 5 111 (ly31P ()) 31 == idM 111 &&
    diffMod5 (ly31P ()) (idM 111)

end CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic
