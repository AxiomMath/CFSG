module

public import Certificates.Data.Kernel.LceSSeg
public import CFSG.Certificates.Kernel.Common.LceS
public import CFSG.Certificates.Kernel.Co1.Data.C4_Sel
public import CFSG.Certificates.Kernel.Co1.Data.C4_Tab

public section

namespace CFSG.KD.C4

open CFSG.KC CFSG.KC.LceSeg

@[expose] noncomputable def okW (i : Nat) : Bool :=
  slOK (LceS.runFacts blk selWT INV nC (nat_lit 6)) JF loF accF i

@[expose] noncomputable def okC (i : Nat) : Bool :=
  slOK (LceS.runCover blk LVs (nat_lit 216) (nat_lit 6)) JV loC accC i

end CFSG.KD.C4

end
