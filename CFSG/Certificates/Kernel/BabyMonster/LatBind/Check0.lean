module

import CFSG.Certificates.Kernel.BabyMonster.Load
public import CFSG.Certificates.Kernel.BabyMonster.LatCheck
public import CFSG.Certificates.Kernel.BabyMonster.LatFast
public import CFSG.Certificates.Kernel.BabyMonster.LatBind.Chunks
public import CFSG.Certificates.Kernel.BabyMonster.Dyadic.Basis

set_option maxRecDepth 200000

#bm_bool CFSG.KD.LatBind len (Nat.beq (CFSG.KC.BM.B64.lenP CH) 43527)
#bm_bool CFSG.KD.LatBind diag (CFSG.KC.BM.Lat.diagOK (CFSG.KC.BM.B64.getP CH 0) CFSG.KC.BM.Dyadic.Bs)
#bm_bool CFSG.KD.LatBind r0f (CFSG.KC.BM.Lat.rowsOKG CFSG.KC.BM.Lat.isB64T CFSG.KC.BM.Lat.b64vT CH CFSG.KC.BM.Dyadic.Bs 0 64)
public theorem CFSG.KD.LatBind.r0 :
    CFSG.KC.BM.Lat.rowsOK CFSG.KD.LatBind.CH CFSG.KC.BM.Dyadic.Bs (nat_lit 0) (nat_lit 64) = true :=
  (CFSG.KC.BM.Lat.rowsOK_fast _ _ _ _).trans CFSG.KD.LatBind.r0f
#bm_bool CFSG.KD.LatBind r1f (CFSG.KC.BM.Lat.rowsOKG CFSG.KC.BM.Lat.isB64T CFSG.KC.BM.Lat.b64vT CH CFSG.KC.BM.Dyadic.Bs 64 64)
public theorem CFSG.KD.LatBind.r1 :
    CFSG.KC.BM.Lat.rowsOK CFSG.KD.LatBind.CH CFSG.KC.BM.Dyadic.Bs (nat_lit 64) (nat_lit 64) = true :=
  (CFSG.KC.BM.Lat.rowsOK_fast _ _ _ _).trans CFSG.KD.LatBind.r1f
#bm_bool CFSG.KD.LatBind r2f (CFSG.KC.BM.Lat.rowsOKG CFSG.KC.BM.Lat.isB64T CFSG.KC.BM.Lat.b64vT CH CFSG.KC.BM.Dyadic.Bs 128 64)
public theorem CFSG.KD.LatBind.r2 :
    CFSG.KC.BM.Lat.rowsOK CFSG.KD.LatBind.CH CFSG.KC.BM.Dyadic.Bs (nat_lit 128) (nat_lit 64) = true :=
  (CFSG.KC.BM.Lat.rowsOK_fast _ _ _ _).trans CFSG.KD.LatBind.r2f
#bm_bool CFSG.KD.LatBind r3f (CFSG.KC.BM.Lat.rowsOKG CFSG.KC.BM.Lat.isB64T CFSG.KC.BM.Lat.b64vT CH CFSG.KC.BM.Dyadic.Bs 192 64)
public theorem CFSG.KD.LatBind.r3 :
    CFSG.KC.BM.Lat.rowsOK CFSG.KD.LatBind.CH CFSG.KC.BM.Dyadic.Bs (nat_lit 192) (nat_lit 64) = true :=
  (CFSG.KC.BM.Lat.rowsOK_fast _ _ _ _).trans CFSG.KD.LatBind.r3f
#bm_bool CFSG.KD.LatBind r4f (CFSG.KC.BM.Lat.rowsOKG CFSG.KC.BM.Lat.isB64T CFSG.KC.BM.Lat.b64vT CH CFSG.KC.BM.Dyadic.Bs 256 64)
public theorem CFSG.KD.LatBind.r4 :
    CFSG.KC.BM.Lat.rowsOK CFSG.KD.LatBind.CH CFSG.KC.BM.Dyadic.Bs (nat_lit 256) (nat_lit 64) = true :=
  (CFSG.KC.BM.Lat.rowsOK_fast _ _ _ _).trans CFSG.KD.LatBind.r4f
#bm_bool CFSG.KD.LatBind r5f (CFSG.KC.BM.Lat.rowsOKG CFSG.KC.BM.Lat.isB64T CFSG.KC.BM.Lat.b64vT CH CFSG.KC.BM.Dyadic.Bs 320 64)
public theorem CFSG.KD.LatBind.r5 :
    CFSG.KC.BM.Lat.rowsOK CFSG.KD.LatBind.CH CFSG.KC.BM.Dyadic.Bs (nat_lit 320) (nat_lit 64) = true :=
  (CFSG.KC.BM.Lat.rowsOK_fast _ _ _ _).trans CFSG.KD.LatBind.r5f
#bm_bool CFSG.KD.LatBind r6f (CFSG.KC.BM.Lat.rowsOKG CFSG.KC.BM.Lat.isB64T CFSG.KC.BM.Lat.b64vT CH CFSG.KC.BM.Dyadic.Bs 384 64)
public theorem CFSG.KD.LatBind.r6 :
    CFSG.KC.BM.Lat.rowsOK CFSG.KD.LatBind.CH CFSG.KC.BM.Dyadic.Bs (nat_lit 384) (nat_lit 64) = true :=
  (CFSG.KC.BM.Lat.rowsOK_fast _ _ _ _).trans CFSG.KD.LatBind.r6f
