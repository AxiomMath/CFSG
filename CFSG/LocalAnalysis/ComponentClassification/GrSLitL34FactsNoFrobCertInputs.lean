module

public import Certificates.Data.CFSGNative.PSL3Four.Certificate

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts

open CFSG.PSL3Four.Native

@[expose] def x7T : Tab := comp 42 g₁T g₂T

@[expose] def x7Pow (t : Tab) : Nat → Tab
  | 0 => idTab 42
  | k + 1 => comp 42 (x7Pow t k) t

@[expose] def noFrobOrbit : Array Tab := (orbitBFS 42 gTabs (gTabs.map (invTab 42)) r₁T 1963).tabs

@[noinline, expose] def noFrobOK : Bool :=
  x7Pow x7T 7 == idTab 42 && !(x7T == idTab 42) &&
    noFrobOrbit.all fun u =>
      !(comp 42 u (comp 42 (comp 42 x7T u) (x7Pow x7T 6)) ==
        comp 42 (comp 42 (comp 42 x7T u) (x7Pow x7T 6)) u)

end CFSG.ComponentClassification.GrSLit.L34Facts
