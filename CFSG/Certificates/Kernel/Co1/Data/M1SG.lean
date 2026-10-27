module

public import CFSG.Certificates.Kernel.Common.DceS
public import CFSG.Certificates.Kernel.Co1.Data.M1S_0
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.NatItemsGz
import CFSG.Certificates.Kernel.Common.Repo

#kc_repo #kc_nat_items_gz CFSG.KD.M1S "CFSG/Certificates/Kernel/Co1/Data/M1S/sg.items.gz" 1175 10830913857674470984
    (SG 0 79)
#kc_select CFSG.KD.M1S sgS SG 79

public noncomputable section

namespace CFSG.KD.M1S

@[expose] def sG (k : Nat) : Bool :=
  Nat.beq (CFSG.KC.DceS.enumRun G4E (CFSG.KC.DceS.packGens MPT 4) 4 nG4 0 4096 (sgS k))
    (sgS (k + 1))

@[expose] def sGc (k : Nat) : Bool :=
  Nat.beq (CFSG.KC.DceS.eCnt
    (CFSG.KC.DceS.enumRun G4E (CFSG.KC.DceS.packGens MPT 4) 4 nG4 0 3072 (sgS k))) (Nat.succ nG4)

end CFSG.KD.M1S

end
