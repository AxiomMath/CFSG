module

public import CFSG.Certificates.Kernel.Fam.Fi24Act.Each
public import CFSG.Certificates.Kernel.Fi24.Data.Fi24B
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.ForallChunks
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.FamFi24Act

theorem nA : Nat.beq CFSG.KD.Fi24B.nAF1 306936 = true := by quickRfl

theorem nC : Nat.beq CFSG.KD.F1.nC 478324 = true := by quickRfl

@[expose] noncomputable def stW (j : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (Nat.add 4 (Nat.mul 8192 j)) 81924 (Nat.beq j 9)

@[expose] noncomputable def stC (j : Nat) : Bool := Nat.beq (CFSG.KD.F1.selST j) (stW j)

end CFSG.KD.FamFi24Act

#kc_each CFSG.KD.FamFi24Act.alC 512 600
#kc_each CFSG.KD.FamFi24Act.stC 0 10

namespace CFSG.KD.FamFi24Act

#kc_forall_chunks ST.all (fun j => stC j = true) 10 CFSG.KD.FamFi24Act.stC 1

end CFSG.KD.FamFi24Act

end
