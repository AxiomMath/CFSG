module

import CFSG.Certificates.Kernel.BabyMonster.Load
public import CFSG.Certificates.Kernel.BabyMonster.LatCheck
public import CFSG.Certificates.Kernel.BabyMonster.LatBind.Chunks
public import CFSG.Certificates.Kernel.BabyMonster.Dyadic.Basis

set_option maxRecDepth 200000

#bm_bool CFSG.KD.LatBind len (Nat.beq (CFSG.KC.BM.B64.lenP CH) 43527)
#bm_bool CFSG.KD.LatBind diag (CFSG.KC.BM.Lat.diagOK (CFSG.KC.BM.B64.getP CH 0) CFSG.KC.BM.Dyadic.Bs)
#bm_bool CFSG.KD.LatBind r0 (CFSG.KC.BM.Lat.rowsOK CH CFSG.KC.BM.Dyadic.Bs 0 64)
#bm_bool CFSG.KD.LatBind r1 (CFSG.KC.BM.Lat.rowsOK CH CFSG.KC.BM.Dyadic.Bs 64 64)
#bm_bool CFSG.KD.LatBind r2 (CFSG.KC.BM.Lat.rowsOK CH CFSG.KC.BM.Dyadic.Bs 128 64)
#bm_bool CFSG.KD.LatBind r3 (CFSG.KC.BM.Lat.rowsOK CH CFSG.KC.BM.Dyadic.Bs 192 64)
#bm_bool CFSG.KD.LatBind r4 (CFSG.KC.BM.Lat.rowsOK CH CFSG.KC.BM.Dyadic.Bs 256 64)
#bm_bool CFSG.KD.LatBind r5 (CFSG.KC.BM.Lat.rowsOK CH CFSG.KC.BM.Dyadic.Bs 320 64)
#bm_bool CFSG.KD.LatBind r6 (CFSG.KC.BM.Lat.rowsOK CH CFSG.KC.BM.Dyadic.Bs 384 64)
