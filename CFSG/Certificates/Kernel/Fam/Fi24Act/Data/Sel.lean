module

import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Fam.Act
public import CFSG.Certificates.Kernel.Fam.Fi24Act.Data.Const
public import CFSG.Certificates.Kernel.Fam.Fi24Act.Data.TabTA
public import CFSG.Certificates.Kernel.Fam.Fi24Act.Data.TabT0
public import CFSG.Certificates.Kernel.Fam.Fi24Act.Data.TabR0
public import CFSG.Certificates.Kernel.Fam.Fi24Act.Data.TabT1
public import CFSG.Certificates.Kernel.Fam.Fi24Act.Data.TabR1
public import CFSG.Certificates.Kernel.Fam.Fi24Act.Data.TabT2
public import CFSG.Certificates.Kernel.Fam.Fi24Act.Data.TabR2
public import CFSG.Certificates.Kernel.Fam.Fi24Act.Data.TabT3
public import CFSG.Certificates.Kernel.Fam.Fi24Act.Data.TabR3
public import CFSG.Certificates.Kernel.Fam.Fi24Act.Data.TabT4
public import CFSG.Certificates.Kernel.Fam.Fi24Act.Data.TabR4
public import CFSG.Certificates.Kernel.Fam.Fi24Act.Data.TabT5
public import CFSG.Certificates.Kernel.Fam.Fi24Act.Data.TabR5
public import CFSG.Certificates.Kernel.Fam.Fi24Act.Data.TabT6
public import CFSG.Certificates.Kernel.Fam.Fi24Act.Data.TabR6
public import CFSG.Certificates.Kernel.Fam.Fi24Act.Data.TabT7
public import CFSG.Certificates.Kernel.Fam.Fi24Act.Data.TabR7
public import CFSG.Certificates.Kernel.Fam.Fi24Act.Data.TabT8
public import CFSG.Certificates.Kernel.Fam.Fi24Act.Data.TabR8
public import CFSG.Certificates.Kernel.Fam.Fi24Act.Data.TabT9
public import CFSG.Certificates.Kernel.Fam.Fi24Act.Data.TabR9
public import CFSG.Certificates.Kernel.Fam.Fi24Act.Data.TabLB
public import CFSG.Certificates.Kernel.Fam.Fi24Act.Data.TabPA

#kc_select CFSG.KD.FamFi24Act TAT TAT 300
#kc_select CFSG.KD.FamFi24Act T0T T0T 300
#kc_select CFSG.KD.FamFi24Act R0T R0T 300
#kc_select CFSG.KD.FamFi24Act T1T T1T 300
#kc_select CFSG.KD.FamFi24Act R1T R1T 300
#kc_select CFSG.KD.FamFi24Act T2T T2T 300
#kc_select CFSG.KD.FamFi24Act R2T R2T 300
#kc_select CFSG.KD.FamFi24Act T3T T3T 300
#kc_select CFSG.KD.FamFi24Act R3T R3T 300
#kc_select CFSG.KD.FamFi24Act T4T T4T 300
#kc_select CFSG.KD.FamFi24Act R4T R4T 300
#kc_select CFSG.KD.FamFi24Act T5T T5T 300
#kc_select CFSG.KD.FamFi24Act R5T R5T 300
#kc_select CFSG.KD.FamFi24Act T6T T6T 300
#kc_select CFSG.KD.FamFi24Act R6T R6T 300
#kc_select CFSG.KD.FamFi24Act T7T T7T 300
#kc_select CFSG.KD.FamFi24Act R7T R7T 300
#kc_select CFSG.KD.FamFi24Act T8T T8T 300
#kc_select CFSG.KD.FamFi24Act R8T R8T 300
#kc_select CFSG.KD.FamFi24Act T9T T9T 300
#kc_select CFSG.KD.FamFi24Act R9T R9T 300
#kc_select CFSG.KD.FamFi24Act LBT LBT 75
#kc_select CFSG.KD.FamFi24Act PAT PAT 600

public section

namespace CFSG.KD.FamFi24Act

@[expose] noncomputable def TA (i : Nat) : Nat :=
  CFSG.KC.Fam.tget TAT 10 24 i

@[expose] noncomputable def T0 (i : Nat) : Nat :=
  CFSG.KC.Fam.tget T0T 10 24 i

@[expose] noncomputable def R0 (i : Nat) : Nat :=
  CFSG.KC.Fam.tget R0T 10 24 i

@[expose] noncomputable def T1 (i : Nat) : Nat :=
  CFSG.KC.Fam.tget T1T 10 24 i

@[expose] noncomputable def R1 (i : Nat) : Nat :=
  CFSG.KC.Fam.tget R1T 10 24 i

@[expose] noncomputable def T2 (i : Nat) : Nat :=
  CFSG.KC.Fam.tget T2T 10 24 i

@[expose] noncomputable def R2 (i : Nat) : Nat :=
  CFSG.KC.Fam.tget R2T 10 24 i

@[expose] noncomputable def T3 (i : Nat) : Nat :=
  CFSG.KC.Fam.tget T3T 10 24 i

@[expose] noncomputable def R3 (i : Nat) : Nat :=
  CFSG.KC.Fam.tget R3T 10 24 i

@[expose] noncomputable def T4 (i : Nat) : Nat :=
  CFSG.KC.Fam.tget T4T 10 24 i

@[expose] noncomputable def R4 (i : Nat) : Nat :=
  CFSG.KC.Fam.tget R4T 10 24 i

@[expose] noncomputable def T5 (i : Nat) : Nat :=
  CFSG.KC.Fam.tget T5T 10 24 i

@[expose] noncomputable def R5 (i : Nat) : Nat :=
  CFSG.KC.Fam.tget R5T 10 24 i

@[expose] noncomputable def T6 (i : Nat) : Nat :=
  CFSG.KC.Fam.tget T6T 10 24 i

@[expose] noncomputable def R6 (i : Nat) : Nat :=
  CFSG.KC.Fam.tget R6T 10 24 i

@[expose] noncomputable def T7 (i : Nat) : Nat :=
  CFSG.KC.Fam.tget T7T 10 24 i

@[expose] noncomputable def R7 (i : Nat) : Nat :=
  CFSG.KC.Fam.tget R7T 10 24 i

@[expose] noncomputable def T8 (i : Nat) : Nat :=
  CFSG.KC.Fam.tget T8T 10 24 i

@[expose] noncomputable def R8 (i : Nat) : Nat :=
  CFSG.KC.Fam.tget R8T 10 24 i

@[expose] noncomputable def T9 (i : Nat) : Nat :=
  CFSG.KC.Fam.tget T9T 10 24 i

@[expose] noncomputable def R9 (i : Nat) : Nat :=
  CFSG.KC.Fam.tget R9T 10 24 i

@[expose] noncomputable def LB (i : Nat) : Nat :=
  CFSG.KC.Fam.tget LBT 12 8 i

@[expose] noncomputable def PA (i : Nat) : Nat :=
  CFSG.KC.Fam.tget PAT 9 40 i

@[expose] noncomputable def HG (g i : Nat) : Nat := (fun j => nIf(Nat.beq g 0, T1 j, nIf(Nat.beq g 1, T2 j, nIf(Nat.beq g 2, T3 j, nIf(Nat.beq g 3, T4 j, nIf(Nat.beq g 4, T5 j, nIf(Nat.beq g 5, T6 j, nIf(Nat.beq g 6, T7 j, nIf(Nat.beq g 7, T8 j, nIf(Nat.beq g 8, T9 j, 0)))))))))) (T0 i)

end CFSG.KD.FamFi24Act

end
