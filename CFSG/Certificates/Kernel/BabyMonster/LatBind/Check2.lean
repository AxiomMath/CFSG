module

import CFSG.Certificates.Kernel.BabyMonster.Load
public import CFSG.Certificates.Kernel.BabyMonster.LatCheck
public import CFSG.Certificates.Kernel.BabyMonster.LatFast
public import CFSG.Certificates.Kernel.BabyMonster.LatBind.Chunks
public import CFSG.Certificates.Kernel.BabyMonster.Dyadic.Basis

set_option maxRecDepth 200000

#bm_bool CFSG.KD.LatBind r14f (CFSG.KC.BM.Lat.rowsOKG CFSG.KC.BM.Lat.isB64T CFSG.KC.BM.Lat.b64vT CH CFSG.KC.BM.Dyadic.Bs 896 64)
public theorem CFSG.KD.LatBind.r14 :
    CFSG.KC.BM.Lat.rowsOK CFSG.KD.LatBind.CH CFSG.KC.BM.Dyadic.Bs (nat_lit 896) (nat_lit 64) = true :=
  (CFSG.KC.BM.Lat.rowsOK_fast _ _ _ _).trans CFSG.KD.LatBind.r14f
#bm_bool CFSG.KD.LatBind r15f (CFSG.KC.BM.Lat.rowsOKG CFSG.KC.BM.Lat.isB64T CFSG.KC.BM.Lat.b64vT CH CFSG.KC.BM.Dyadic.Bs 960 64)
public theorem CFSG.KD.LatBind.r15 :
    CFSG.KC.BM.Lat.rowsOK CFSG.KD.LatBind.CH CFSG.KC.BM.Dyadic.Bs (nat_lit 960) (nat_lit 64) = true :=
  (CFSG.KC.BM.Lat.rowsOK_fast _ _ _ _).trans CFSG.KD.LatBind.r15f
#bm_bool CFSG.KD.LatBind r16f (CFSG.KC.BM.Lat.rowsOKG CFSG.KC.BM.Lat.isB64T CFSG.KC.BM.Lat.b64vT CH CFSG.KC.BM.Dyadic.Bs 1024 64)
public theorem CFSG.KD.LatBind.r16 :
    CFSG.KC.BM.Lat.rowsOK CFSG.KD.LatBind.CH CFSG.KC.BM.Dyadic.Bs (nat_lit 1024) (nat_lit 64) = true :=
  (CFSG.KC.BM.Lat.rowsOK_fast _ _ _ _).trans CFSG.KD.LatBind.r16f
#bm_bool CFSG.KD.LatBind r17f (CFSG.KC.BM.Lat.rowsOKG CFSG.KC.BM.Lat.isB64T CFSG.KC.BM.Lat.b64vT CH CFSG.KC.BM.Dyadic.Bs 1088 64)
public theorem CFSG.KD.LatBind.r17 :
    CFSG.KC.BM.Lat.rowsOK CFSG.KD.LatBind.CH CFSG.KC.BM.Dyadic.Bs (nat_lit 1088) (nat_lit 64) = true :=
  (CFSG.KC.BM.Lat.rowsOK_fast _ _ _ _).trans CFSG.KD.LatBind.r17f
#bm_bool CFSG.KD.LatBind r18f (CFSG.KC.BM.Lat.rowsOKG CFSG.KC.BM.Lat.isB64T CFSG.KC.BM.Lat.b64vT CH CFSG.KC.BM.Dyadic.Bs 1152 64)
public theorem CFSG.KD.LatBind.r18 :
    CFSG.KC.BM.Lat.rowsOK CFSG.KD.LatBind.CH CFSG.KC.BM.Dyadic.Bs (nat_lit 1152) (nat_lit 64) = true :=
  (CFSG.KC.BM.Lat.rowsOK_fast _ _ _ _).trans CFSG.KD.LatBind.r18f
#bm_bool CFSG.KD.LatBind r19f (CFSG.KC.BM.Lat.rowsOKG CFSG.KC.BM.Lat.isB64T CFSG.KC.BM.Lat.b64vT CH CFSG.KC.BM.Dyadic.Bs 1216 64)
public theorem CFSG.KD.LatBind.r19 :
    CFSG.KC.BM.Lat.rowsOK CFSG.KD.LatBind.CH CFSG.KC.BM.Dyadic.Bs (nat_lit 1216) (nat_lit 64) = true :=
  (CFSG.KC.BM.Lat.rowsOK_fast _ _ _ _).trans CFSG.KD.LatBind.r19f
#bm_bool CFSG.KD.LatBind r20f (CFSG.KC.BM.Lat.rowsOKG CFSG.KC.BM.Lat.isB64T CFSG.KC.BM.Lat.b64vT CH CFSG.KC.BM.Dyadic.Bs 1280 64)
public theorem CFSG.KD.LatBind.r20 :
    CFSG.KC.BM.Lat.rowsOK CFSG.KD.LatBind.CH CFSG.KC.BM.Dyadic.Bs (nat_lit 1280) (nat_lit 64) = true :=
  (CFSG.KC.BM.Lat.rowsOK_fast _ _ _ _).trans CFSG.KD.LatBind.r20f
