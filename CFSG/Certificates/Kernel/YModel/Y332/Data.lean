module

public import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.YModel.Texts.YM332P
public import Certificates.Data.Kernel.YModel.Model
import CFSG.Certificates.Kernel.Common.Benes

public section

namespace CFSG.KD.YMY332

open CFSG.KC CFSG.KC.YModel CFSG.KC.MonsterConv.Perm

#kc_benes CFSG.KD.YMY332 N 0 9 15 fun _ c => colPlanes (signExt 28160 (CFSG.KD.YM332P.F c)) 32 28162 15 0
#kc_select CFSG.KD.YMY332 Nf N 9

@[expose] noncomputable def letChk (c : Nat) : Bool :=
  andB (Nat.blt (CFSG.KD.YM332P.F c) (Nat.shiftLeft 1 (32 * 28160)))
    (andB (letOK 15 28162 (signExt 28160 (CFSG.KD.YM332P.F c)) (Nf c))
      (Nat.beq (lget CFSG.KD.YM332P.El c) 28160))

end CFSG.KD.YMY332

end
