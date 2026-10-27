module

public import Certificates.Data.Kernel.K3
public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3SelK3SporDefs
public import CFSG.Certificates.Kernel.Spor.RawDefs

public section

namespace CFSG.KC.K3

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Sporadic.Th.Native CFSG.EvenSmallLie.Child3.SelK3

@[expose] def instrOf (K : K3C) (t : Nat) : Instr :=
  if K.OP t = 0 then .mu (K.A1 t) (K.A2 t) (K.A3 t)
  else if K.OP t = 1 then .pwr (K.A1 t) (K.A2 t) (K.A3 t) else .iv (K.A1 t) (K.A2 t)

@[expose] def witOf (K : K3C) (j : Nat) : Wit :=
  if K.WT j = 0 then .z4 (K.WU j) else .v4 (K.WU j) (K.WV j)

@[expose] noncomputable def tblOf (K : K3C) (P : Nat) : Table := (unpack K.n K.w P).map UInt32.ofNat

end CFSG.KC.K3

end
