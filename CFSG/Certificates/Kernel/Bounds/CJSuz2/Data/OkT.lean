module

public import Certificates.Data.Kernel.LceSSeg
public import CFSG.Certificates.Kernel.Bounds.CJSuz2.Data.T_Sel
public import CFSG.Certificates.Kernel.Bounds.CJSuz2.Data.JFT
public import CFSG.Certificates.Kernel.Bounds.CJSuz2.Data.TabT
public import CFSG.Certificates.Kernel.Common.LabZ

public section

namespace CFSG.KD.CJSuz2T

open CFSG.KC CFSG.KC.LceSeg

@[expose] noncomputable def okW (i : Nat) : Bool :=
  slOK (LceS.runFacts blk selWT INV nC (nat_lit 10)) JF loF accF i

@[expose] noncomputable def okC (i : Nat) : Bool :=
  slOK (LceS.runCover blk LVs (nat_lit 1169643) (nat_lit 10)) JV loC accC i

@[expose] noncomputable def okL (i : Nat) : Bool :=
  slOK (LabF.runLab selWT LB HS) JF loF accL i

@[expose] noncomputable def codeT (i : Nat) : Nat :=
  Loop.strictN (Nat.shiftRight i (nat_lit 12)) (fun q =>
    Nat.land (Nat.shiftRight (LCs q) (Nat.mul (nat_lit 5) (Nat.land i (nat_lit 4095))))
      (nat_lit 31))

@[expose] noncomputable def okZ (i : Nat) : Bool :=
  slOK (LabZ.runLabC selWT codeT HS) JF loF accL i

@[expose] noncomputable def okY : Bool :=
  LabF.cycOK blk selWT LB (nat_lit 1169643) (CY (nat_lit 0)) (CY (nat_lit 1)) (CY (nat_lit 2))
    (LabF.entStk
      (nat_lit 28380414028753969466561515933501938199330878594519746088102349021547335800))

end CFSG.KD.CJSuz2T

end
