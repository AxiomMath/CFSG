module

public import Certificates.Data.Kernel.KDense.Letters
public import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.NatItemsGz
import CFSG.Certificates.Kernel.Common.Repo

public section

set_option maxRecDepth 100000

#kc_repo #kc_nat_items_gz CFSG.KD.KDF "CFSG/Certificates/Kernel/KDense/Data/fix.items.gz" 2354139 16226376967156215868
    TH OCT DU1 KT keyA keyD xiNet xiSgn pout pi6 doct sgOddUp sgWLo sgWUp I0X I0A I0W I1X I1A I1W
    I2X I2A I2W

namespace CFSG.KD.KDF

open CFSG.KC.KDense

@[expose] noncomputable def F : Fix := ⟨keyA, keyD, xiNet, xiSgn, pout, pi6, doct, sgOddUp, sgWLo, sgWUp⟩

@[expose] noncomputable def I (x : Nat) : St :=
  Bool.rec (motive := fun _ => St) (Bool.rec (motive := fun _ => St) (mkSt I2X I2A I2W) (mkSt I1X I1A I1W)
    (Nat.beq x 1)) (mkSt I0X I0A I0W) (Nat.beq x 0)

end CFSG.KD.KDF

end
