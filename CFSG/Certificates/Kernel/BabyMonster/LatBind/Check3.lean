module

import CFSG.Certificates.Kernel.BabyMonster.Load
public import CFSG.Certificates.Kernel.BabyMonster.LatCheck
public import CFSG.Certificates.Kernel.BabyMonster.LatFast
public import CFSG.Certificates.Kernel.BabyMonster.LatBind.Chunks
public import CFSG.Certificates.Kernel.BabyMonster.Dyadic.Basis

set_option maxRecDepth 200000

#bm_bool CFSG.KD.LatBind r21f (CFSG.KC.BM.Lat.rowsOKG CFSG.KC.BM.Lat.isB64T CFSG.KC.BM.Lat.b64vT CH CFSG.KC.BM.Dyadic.Bs 1344 64)
public theorem CFSG.KD.LatBind.r21 :
    CFSG.KC.BM.Lat.rowsOK CFSG.KD.LatBind.CH CFSG.KC.BM.Dyadic.Bs (nat_lit 1344) (nat_lit 64) = true :=
  (CFSG.KC.BM.Lat.rowsOK_fast _ _ _ _).trans CFSG.KD.LatBind.r21f
#bm_bool CFSG.KD.LatBind r22f (CFSG.KC.BM.Lat.rowsOKG CFSG.KC.BM.Lat.isB64T CFSG.KC.BM.Lat.b64vT CH CFSG.KC.BM.Dyadic.Bs 1408 64)
public theorem CFSG.KD.LatBind.r22 :
    CFSG.KC.BM.Lat.rowsOK CFSG.KD.LatBind.CH CFSG.KC.BM.Dyadic.Bs (nat_lit 1408) (nat_lit 64) = true :=
  (CFSG.KC.BM.Lat.rowsOK_fast _ _ _ _).trans CFSG.KD.LatBind.r22f
#bm_bool CFSG.KD.LatBind r23f (CFSG.KC.BM.Lat.rowsOKG CFSG.KC.BM.Lat.isB64T CFSG.KC.BM.Lat.b64vT CH CFSG.KC.BM.Dyadic.Bs 1472 64)
public theorem CFSG.KD.LatBind.r23 :
    CFSG.KC.BM.Lat.rowsOK CFSG.KD.LatBind.CH CFSG.KC.BM.Dyadic.Bs (nat_lit 1472) (nat_lit 64) = true :=
  (CFSG.KC.BM.Lat.rowsOK_fast _ _ _ _).trans CFSG.KD.LatBind.r23f
#bm_bool CFSG.KD.LatBind r24 (CFSG.KC.BM.Lat.rowsOK CH CFSG.KC.BM.Dyadic.Bs 1536 64)
#bm_bool CFSG.KD.LatBind r25 (CFSG.KC.BM.Lat.rowsOK CH CFSG.KC.BM.Dyadic.Bs 1600 64)
#bm_bool CFSG.KD.LatBind r26 (CFSG.KC.BM.Lat.rowsOK CH CFSG.KC.BM.Dyadic.Bs 1664 64)
#bm_bool CFSG.KD.LatBind r27 (CFSG.KC.BM.Lat.rowsOK CH CFSG.KC.BM.Dyadic.Bs 1728 64)
