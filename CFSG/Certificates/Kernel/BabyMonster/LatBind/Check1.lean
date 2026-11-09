module

import CFSG.Certificates.Kernel.BabyMonster.Load
public import CFSG.Certificates.Kernel.BabyMonster.LatCheck
public import CFSG.Certificates.Kernel.BabyMonster.LatFast
public import CFSG.Certificates.Kernel.BabyMonster.LatBind.Chunks
public import CFSG.Certificates.Kernel.BabyMonster.Dyadic.Basis

set_option maxRecDepth 200000

#bm_bool CFSG.KD.LatBind r7f (CFSG.KC.BM.Lat.rowsOKG CFSG.KC.BM.Lat.isB64T CFSG.KC.BM.Lat.b64vT CH CFSG.KC.BM.Dyadic.Bs 448 64)
public theorem CFSG.KD.LatBind.r7 :
    CFSG.KC.BM.Lat.rowsOK CFSG.KD.LatBind.CH CFSG.KC.BM.Dyadic.Bs (nat_lit 448) (nat_lit 64) = true :=
  (CFSG.KC.BM.Lat.rowsOK_fast _ _ _ _).trans CFSG.KD.LatBind.r7f
#bm_bool CFSG.KD.LatBind r8f (CFSG.KC.BM.Lat.rowsOKG CFSG.KC.BM.Lat.isB64T CFSG.KC.BM.Lat.b64vT CH CFSG.KC.BM.Dyadic.Bs 512 64)
public theorem CFSG.KD.LatBind.r8 :
    CFSG.KC.BM.Lat.rowsOK CFSG.KD.LatBind.CH CFSG.KC.BM.Dyadic.Bs (nat_lit 512) (nat_lit 64) = true :=
  (CFSG.KC.BM.Lat.rowsOK_fast _ _ _ _).trans CFSG.KD.LatBind.r8f
#bm_bool CFSG.KD.LatBind r9f (CFSG.KC.BM.Lat.rowsOKG CFSG.KC.BM.Lat.isB64T CFSG.KC.BM.Lat.b64vT CH CFSG.KC.BM.Dyadic.Bs 576 64)
public theorem CFSG.KD.LatBind.r9 :
    CFSG.KC.BM.Lat.rowsOK CFSG.KD.LatBind.CH CFSG.KC.BM.Dyadic.Bs (nat_lit 576) (nat_lit 64) = true :=
  (CFSG.KC.BM.Lat.rowsOK_fast _ _ _ _).trans CFSG.KD.LatBind.r9f
#bm_bool CFSG.KD.LatBind r10f (CFSG.KC.BM.Lat.rowsOKG CFSG.KC.BM.Lat.isB64T CFSG.KC.BM.Lat.b64vT CH CFSG.KC.BM.Dyadic.Bs 640 64)
public theorem CFSG.KD.LatBind.r10 :
    CFSG.KC.BM.Lat.rowsOK CFSG.KD.LatBind.CH CFSG.KC.BM.Dyadic.Bs (nat_lit 640) (nat_lit 64) = true :=
  (CFSG.KC.BM.Lat.rowsOK_fast _ _ _ _).trans CFSG.KD.LatBind.r10f
#bm_bool CFSG.KD.LatBind r11f (CFSG.KC.BM.Lat.rowsOKG CFSG.KC.BM.Lat.isB64T CFSG.KC.BM.Lat.b64vT CH CFSG.KC.BM.Dyadic.Bs 704 64)
public theorem CFSG.KD.LatBind.r11 :
    CFSG.KC.BM.Lat.rowsOK CFSG.KD.LatBind.CH CFSG.KC.BM.Dyadic.Bs (nat_lit 704) (nat_lit 64) = true :=
  (CFSG.KC.BM.Lat.rowsOK_fast _ _ _ _).trans CFSG.KD.LatBind.r11f
#bm_bool CFSG.KD.LatBind r12f (CFSG.KC.BM.Lat.rowsOKG CFSG.KC.BM.Lat.isB64T CFSG.KC.BM.Lat.b64vT CH CFSG.KC.BM.Dyadic.Bs 768 64)
public theorem CFSG.KD.LatBind.r12 :
    CFSG.KC.BM.Lat.rowsOK CFSG.KD.LatBind.CH CFSG.KC.BM.Dyadic.Bs (nat_lit 768) (nat_lit 64) = true :=
  (CFSG.KC.BM.Lat.rowsOK_fast _ _ _ _).trans CFSG.KD.LatBind.r12f
#bm_bool CFSG.KD.LatBind r13f (CFSG.KC.BM.Lat.rowsOKG CFSG.KC.BM.Lat.isB64T CFSG.KC.BM.Lat.b64vT CH CFSG.KC.BM.Dyadic.Bs 832 64)
public theorem CFSG.KD.LatBind.r13 :
    CFSG.KC.BM.Lat.rowsOK CFSG.KD.LatBind.CH CFSG.KC.BM.Dyadic.Bs (nat_lit 832) (nat_lit 64) = true :=
  (CFSG.KC.BM.Lat.rowsOK_fast _ _ _ _).trans CFSG.KD.LatBind.r13f
