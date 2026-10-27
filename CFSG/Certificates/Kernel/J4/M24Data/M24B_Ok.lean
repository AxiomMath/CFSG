module

public import Certificates.Data.Kernel.LceSSeg
public import CFSG.Certificates.Kernel.Common.LceS
public import CFSG.Certificates.Kernel.J4.M24Data.M24B_Sel
public import CFSG.Certificates.Kernel.J4.M24Data.M24B_Tab

public section

namespace CFSG.KD.M24B

open CFSG.KC CFSG.KC.LceSeg

@[expose] noncomputable def okW (i : Nat) : Bool :=
  slOK (LceS.runFacts blk selWT INV nC (nat_lit 14)) JF loF accF i

@[expose] noncomputable def okC (i : Nat) : Bool :=
  slOK (LceS.runCover blk LVs (nat_lit 3848842) (nat_lit 14)) JV loC accC i

end CFSG.KD.M24B

end
