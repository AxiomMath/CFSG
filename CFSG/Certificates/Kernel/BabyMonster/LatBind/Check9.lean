module

import CFSG.Certificates.Kernel.BabyMonster.Load
public import CFSG.Certificates.Kernel.BabyMonster.LatCheck
public import CFSG.Certificates.Kernel.BabyMonster.LatBind.Chunks
public import CFSG.Certificates.Kernel.BabyMonster.Dyadic.Basis

set_option maxRecDepth 200000

#bm_bool CFSG.KD.LatBind r63 (CFSG.KC.BM.Lat.rowsOK CH CFSG.KC.BM.Dyadic.Bs 4032 64)
#bm_bool CFSG.KD.LatBind r64 (CFSG.KC.BM.Lat.rowsOK CH CFSG.KC.BM.Dyadic.Bs 4096 64)
#bm_bool CFSG.KD.LatBind r65 (CFSG.KC.BM.Lat.rowsOK CH CFSG.KC.BM.Dyadic.Bs 4160 64)
#bm_bool CFSG.KD.LatBind r66 (CFSG.KC.BM.Lat.rowsOK CH CFSG.KC.BM.Dyadic.Bs 4224 64)
#bm_bool CFSG.KD.LatBind r67 (CFSG.KC.BM.Lat.rowsOK CH CFSG.KC.BM.Dyadic.Bs 4288 64)
#bm_bool CFSG.KD.LatBind r68 (CFSG.KC.BM.Lat.rowsOK CH CFSG.KC.BM.Dyadic.Bs 4352 19)
