module

public import CFSG.Certificates.Kernel.Orders.Cert
public import CFSG.Certificates.Kernel.Orders.HN.Data.Sel
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

#kc_repo #kc_json_gz CFSG.KD.OrdHN "CFSG/Certificates/Kernel/Orders/HN/Checks/data/tab.json.gz"
  22707 12382433098311074118
  (S2.PR : Nat) (S2.BL : Nat) (S2.PW : Nat) (S2.PC : List Nat) (S2.TC : List (List Nat))
  (S2.N : List Nat) (S2.SC : List (List Nat)) (S2.SS : List Nat)
  (S3.PR : Nat) (S3.BL : Nat) (S3.PW : Nat) (S3.PC : List Nat) (S3.TC : List (List Nat))
  (S3.N : List Nat) (S3.SC : List (List Nat)) (S3.SS : List Nat)
  (S5.PR : Nat) (S5.BL : Nat) (S5.TC : List (List Nat))
  (S5.N : List Nat) (S5.SC : List (List Nat)) (S5.SS : List Nat)
  (WS : List (List Nat)) (WSt : List Nat)

public noncomputable section

namespace CFSG.KD.OrdHN

@[expose] def wsC (j : Nat) : Bool :=
  Nat.beq (CFSG.KC.Ord.runSlp RW (CFSG.KC.Ord.mulR 5 13 0x6c1 0x85 9 L H CM RM)
    (CFSG.KC.Ord.validM 5 0x38245 L H) ONE (WS.getD j []) (WSt.getD j 0)) (WSt.getD (j + 1) 0)

end CFSG.KD.OrdHN

end
