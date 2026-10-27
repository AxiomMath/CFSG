module

import CFSG.Certificates.Kernel.BabyMonster.Load
public import CFSG.Certificates.Kernel.BabyMonster.F2
public import CFSG.Certificates.Kernel.BabyMonster.Render
public import CFSG.Certificates.Kernel.BabyMonster.NativePair.Data0
public import CFSG.Certificates.Kernel.BabyMonster.NativePair.Data1
public import CFSG.Certificates.Kernel.BabyMonster.NativePair.Data2
public import CFSG.Certificates.Kernel.BabyMonster.NativePair.Data3
public import CFSG.Certificates.Kernel.BabyMonster.Seeds.Data0
public import CFSG.Certificates.Kernel.BabyMonster.NativePair24.Data0
public import CFSG.Certificates.Kernel.BabyMonster.NativePair24.Data1
public import CFSG.Certificates.Kernel.BabyMonster.NativePair24.Data2
public import CFSG.Certificates.Kernel.BabyMonster.NativePair24.Data3
public import CFSG.Certificates.Kernel.BabyMonster.NativePair24.Data4
public import CFSG.Certificates.Kernel.BabyMonster.NativePair24.Data5
public import CFSG.Certificates.Kernel.BabyMonster.NativePair24.Vecs

#bm_mul CFSG.KC.BM.NativePair24 cPR_sq4 PR_sq3 [PR_sq3] PR_sq4 []
#bm_mul CFSG.KC.BM.NativePair24 copr_p opr_pp0 [PR_sq4] opr_p []
#bm_mul CFSG.KC.BM.NativePair24 opr_pow opr_p [PR] I []
#bm_bool CFSG.KC.BM.NativePair24 opr_orb (CFSG.KC.BM.andB (CFSG.KC.BM.andB (CFSG.KC.BM.onlyRows Vopr 23) (Nat.beq (CFSG.KC.BM.rowsBlk Vopr 0 1) 1)) (CFSG.KC.BM.andB (Nat.beq (CFSG.KC.BM.rowsBlk Vopr 1 22) (CFSG.KC.BM.rowsBlk (CFSG.KC.BM.mulS PR Vopr) 0 22)) (CFSG.KC.BM.allDistinct (CFSG.KC.BM.rowList [Vopr] 23))))
