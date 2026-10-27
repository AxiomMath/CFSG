
module

public import CFSG.Certificates.Kernel.Th.Spec.MirrorBase

public import CFSG.Sporadic.Th.Max3.Data

public section

namespace CFSG.KC.Th.Spec.Mir

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3 CFSG.Sporadic.ThSchreier

@[expose] def m3z (RA RB : Array V4) : Array V4 :=
  powRows (wordRows (m3x RA RB) (m3y RA RB) zWord) zExp

end CFSG.KC.Th.Spec.Mir

end
