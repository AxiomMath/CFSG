module

import CFSG.Certificates.Kernel.BabyMonster.Load
public import CFSG.Certificates.Kernel.BabyMonster.LatCheck
public import CFSG.Certificates.Kernel.BabyMonster.LatBind.Chunks
public import CFSG.Certificates.Kernel.BabyMonster.Dyadic.Basis

set_option maxRecDepth 200000

#bm_bool CFSG.KD.LatBind r14 (CFSG.KC.BM.Lat.rowsOK CH CFSG.KC.BM.Dyadic.Bs 896 64)
#bm_bool CFSG.KD.LatBind r15 (CFSG.KC.BM.Lat.rowsOK CH CFSG.KC.BM.Dyadic.Bs 960 64)
#bm_bool CFSG.KD.LatBind r16 (CFSG.KC.BM.Lat.rowsOK CH CFSG.KC.BM.Dyadic.Bs 1024 64)
#bm_bool CFSG.KD.LatBind r17 (CFSG.KC.BM.Lat.rowsOK CH CFSG.KC.BM.Dyadic.Bs 1088 64)
#bm_bool CFSG.KD.LatBind r18 (CFSG.KC.BM.Lat.rowsOK CH CFSG.KC.BM.Dyadic.Bs 1152 64)
#bm_bool CFSG.KD.LatBind r19 (CFSG.KC.BM.Lat.rowsOK CH CFSG.KC.BM.Dyadic.Bs 1216 64)
#bm_bool CFSG.KD.LatBind r20 (CFSG.KC.BM.Lat.rowsOK CH CFSG.KC.BM.Dyadic.Bs 1280 64)
