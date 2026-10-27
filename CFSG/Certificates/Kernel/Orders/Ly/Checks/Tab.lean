module

public import CFSG.Certificates.Kernel.Orders.Cert
public import CFSG.Certificates.Kernel.Orders.Ly.Data.Sel
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

#kc_repo #kc_json_gz CFSG.KD.OrdLy "CFSG/Certificates/Kernel/Orders/Ly/Checks/data/tab.json.gz"
  89765 13034234228671940219
  (S2.PR : Nat) (S2.BL : Nat) (S2.PW : Nat) (S2.PC : List Nat) (S2.TC : List (List Nat))
  (S2.N : List Nat) (S2.SC : List (List Nat)) (S2.SS : List Nat)
  (S3.PR : Nat) (S3.BL : Nat) (S3.PW : Nat) (S3.PC : List Nat) (S3.TC : List (List Nat))
  (S3.N : List Nat) (S3.SC : List (List Nat)) (S3.SS : List Nat)
  (S5.PR : Nat) (S5.BL : Nat) (S5.TC : List (List Nat))
  (S5.N : List Nat) (S5.SC : List (List Nat)) (S5.SS : List Nat)
  (WS : List (List Nat)) (WSt : List Nat)

public noncomputable section

namespace CFSG.KD.OrdLy

@[expose] def wsC (j : Nat) : Bool :=
  Nat.beq (CFSG.KC.Ord.runSlp RW (CFSG.KC.Ord.mulR 5 12 0x534 0x6f 8 L H CM RM)
    (CFSG.KC.Ord.validM 5 0x2418c L H) ONE (WS.getD j []) (WSt.getD j 0)) (WSt.getD (j + 1) 0)

end CFSG.KD.OrdLy

end
