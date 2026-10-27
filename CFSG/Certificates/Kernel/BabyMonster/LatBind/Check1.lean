module

import CFSG.Certificates.Kernel.BabyMonster.Load
public import CFSG.Certificates.Kernel.BabyMonster.LatCheck
public import CFSG.Certificates.Kernel.BabyMonster.LatBind.Chunks
public import CFSG.Certificates.Kernel.BabyMonster.Dyadic.Basis

set_option maxRecDepth 200000

#bm_bool CFSG.KD.LatBind r7 (CFSG.KC.BM.Lat.rowsOK CH CFSG.KC.BM.Dyadic.Bs 448 64)
#bm_bool CFSG.KD.LatBind r8 (CFSG.KC.BM.Lat.rowsOK CH CFSG.KC.BM.Dyadic.Bs 512 64)
#bm_bool CFSG.KD.LatBind r9 (CFSG.KC.BM.Lat.rowsOK CH CFSG.KC.BM.Dyadic.Bs 576 64)
#bm_bool CFSG.KD.LatBind r10 (CFSG.KC.BM.Lat.rowsOK CH CFSG.KC.BM.Dyadic.Bs 640 64)
#bm_bool CFSG.KD.LatBind r11 (CFSG.KC.BM.Lat.rowsOK CH CFSG.KC.BM.Dyadic.Bs 704 64)
#bm_bool CFSG.KD.LatBind r12 (CFSG.KC.BM.Lat.rowsOK CH CFSG.KC.BM.Dyadic.Bs 768 64)
#bm_bool CFSG.KD.LatBind r13 (CFSG.KC.BM.Lat.rowsOK CH CFSG.KC.BM.Dyadic.Bs 832 64)
