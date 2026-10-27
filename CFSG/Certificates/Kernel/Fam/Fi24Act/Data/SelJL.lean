module

import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Fam.Act
public import CFSG.Certificates.Kernel.Fam.Fi24Act.Data.TabTJ
public import CFSG.Certificates.Kernel.Fam.Fi24Act.Data.TabRJ
public import CFSG.Certificates.Kernel.Fam.Fi24Act.Data.TabTL
public import CFSG.Certificates.Kernel.Fam.Fi24Act.Data.TabRL

#kc_select CFSG.KD.FamFi24Act TJT TJT 300
#kc_select CFSG.KD.FamFi24Act RJT RJT 300
#kc_select CFSG.KD.FamFi24Act TLT TLT 300
#kc_select CFSG.KD.FamFi24Act RLT RLT 300

public section

namespace CFSG.KD.FamFi24Act

@[expose] noncomputable def TJ (i : Nat) : Nat :=
  CFSG.KC.Fam.tget TJT 10 24 i

@[expose] noncomputable def RJ (i : Nat) : Nat :=
  CFSG.KC.Fam.tget RJT 10 24 i

@[expose] noncomputable def TL (i : Nat) : Nat :=
  CFSG.KC.Fam.tget TLT 10 24 i

@[expose] noncomputable def RL (i : Nat) : Nat :=
  CFSG.KC.Fam.tget RLT 10 24 i

end CFSG.KD.FamFi24Act

end
