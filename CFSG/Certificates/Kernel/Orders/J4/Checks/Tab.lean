module

public import CFSG.Certificates.Kernel.Orders.Cert
public import CFSG.Certificates.Kernel.Orders.J4.Data.Sel
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

#kc_repo #kc_json_gz CFSG.KD.OrdJ4 "CFSG/Certificates/Kernel/Orders/J4/Checks/data/tab.json.gz"
  63203 13690591095228647784
  (S2.PR : Nat) (S2.BL : Nat) (S2.TC : List (List Nat))
  (S2.N : List Nat) (S2.SC : List (List Nat)) (S2.SS : List Nat)
  (S3.PR : Nat) (S3.BL : Nat) (S3.PW : Nat) (S3.PC : List Nat) (S3.TC : List (List Nat))
  (S3.N : List Nat) (S3.SC : List (List Nat)) (S3.SS : List Nat)
  (S11.PR : Nat) (S11.BL : Nat) (S11.PW : Nat) (S11.PC : List Nat) (S11.TC : List (List Nat))
  (S11.N : List Nat) (S11.SC : List (List Nat)) (S11.SS : List Nat)
  (WS : List (List Nat)) (WSt : List Nat)

public noncomputable section

namespace CFSG.KD.OrdJ4

@[expose] def wsC (j : Nat) : Bool :=
  Nat.beq (CFSG.KC.Ord.runSlp RW (CFSG.KC.Ord.mulR 2 8 0x380 0x70 6 L H CM RM)
    (CFSG.KC.Ord.validM 2 0x18800 L H) ONE (WS.getD j []) (WSt.getD j 0)) (WSt.getD (j + 1) 0)

end CFSG.KD.OrdJ4

end
