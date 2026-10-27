module

import CFSG.Certificates.Kernel.BabyMonster.Load
public import CFSG.Certificates.Kernel.BabyMonster.LatSound
public import CFSG.Certificates.Kernel.BabyMonster.LatBind.Chunks
public import CFSG.Certificates.Kernel.BabyMonster.Dyadic.Basis

set_option maxRecDepth 200000

#bm_bool CFSG.KD.LatBind nz (CFSG.KC.BM.Lat.nzAll CFSG.KC.BM.Dyadic.Bs)
#bm_bool CFSG.KD.LatBind last (CFSG.KC.BM.Lat.lastLenOK CH)
