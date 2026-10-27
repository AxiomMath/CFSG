module

import all Certificates.Data.Census
public import Certificates.Data.Census
public import Certificates.Data.Kernel.GilmanCensus.Twin

public section

namespace Certificates.GilmanCensusK

open Certificates.Census

theorem typeName_eq (n k : Nat) : typeName n k = typeNameK n k := by
  unfold typeName typeNameK
  rfl

end Certificates.GilmanCensusK

end
