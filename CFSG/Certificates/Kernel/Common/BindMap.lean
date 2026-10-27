module

public import CFSG.Certificates.Kernel.Common.Bind

public section

namespace CFSG.KC.Bind

@[expose] noncomputable def ofPairs (ps : List (Nat × Nat)) : Nat :=
  ps.foldl (fun M p => mset M p.1 p.2) allFF

end CFSG.KC.Bind

end
