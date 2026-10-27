module

public import Certificates.Data.Kernel.LceSSeg
public import CFSG.Certificates.Kernel.Bounds.CJSuz2.Data.T_Sel
public import CFSG.Certificates.Kernel.Bounds.CJSuz2.Data.B_Sel
public import CFSG.Certificates.Kernel.Bounds.CJSuz2.Data.JFT
public import CFSG.Certificates.Kernel.Bounds.CJSuz2.Data.TabT

public section

namespace CFSG.KD.CJSuz2T

open CFSG.KC CFSG.KC.LceSeg

@[expose] noncomputable def okW (i : Nat) : Bool :=
  slOK (LceS.runFacts blk selWT INV nC (nat_lit 10)) JF loF accF i

@[expose] noncomputable def okC (i : Nat) : Bool :=
  slOK (LceS.runCover blk LVs (nat_lit 1169643) (nat_lit 10)) JV loC accC i

@[expose] noncomputable def okL (i : Nat) : Bool :=
  slOK (LabF.runLab selWT LB HS) JF loF accL i

@[expose] noncomputable def okY (k : Nat) : Bool :=
  LabF.cycOK blk selWT LB (nat_lit 1169643) (CY (Nat.mul (nat_lit 3) k))
    (CY (Nat.add (Nat.mul (nat_lit 3) k) (nat_lit 1))) (CY (Nat.add (Nat.mul (nat_lit 3) k) (nat_lit 2)))
    (LabF.entStk (CFSG.KD.CJSuz2B.selRT k))

end CFSG.KD.CJSuz2T

end
