module

public import CFSG.Sporadic.Schreier.LyCheckCover

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic

open CFSG.Sporadic.Ly.Native CFSG.Sporadic.He.Native CFSG.Sporadic.LySchreier.Native

set_option compiler.extract_closed false

@[expose] def lyDihWord : List Int := [2, 1, 2, 2, 1, 2, 1, 2]

@[expose] def lyDihWordInv : List Int := [-2, -1, -2, -1, -2, -2, -1, -2]

@[expose] def lySeedWordM (w : List Int) : Mat :=
  evalWordM seedM (seedMInv (powM 5 111 matB 4)) w

@[expose] def lyDihC (_ : Unit := ()) : Mat := lySeedWordM lyDihWord

@[expose] def lyDihCi (_ : Unit := ()) : Mat := lySeedWordM lyDihWordInv

@[expose] def lyDihP (_ : Unit := ()) : Mat :=
  mulM 5 111 matA (mulM 5 111 (mulM 5 111 (lyDihC ()) matA) (lyDihCi ()))

@[expose] def lyDihCheck (_ : Unit := ()) : Bool :=
  mulM 5 111 (lyDihC ()) (lyDihCi ()) == idM 111 && powM 5 111 (lyDihP ()) 37 == idM 111 &&
    diffMod5 (lyDihP ()) (idM 111)

end CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic
