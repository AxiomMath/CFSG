module

import CFSG.Certificates.Kernel.BabyMonster.Load
public import CFSG.Certificates.Kernel.BabyMonster.PktCheck
public import CFSG.Certificates.Kernel.BabyMonster.PktBind.Text
public import CFSG.Certificates.Kernel.BabyMonster.Dyadic.Gens
public import CFSG.Certificates.Kernel.BabyMonster.Native.Small

set_option maxRecDepth 200000

#bm_bool CFSG.KD.PktBind mono0 (CFSG.KC.BM.Pkt.monoOK (CFSG.KC.BM.Pkt.lineOf CH S 1) (CFSG.KC.BM.nthN CFSG.KC.BM.Dyadic.G0.b0 0))
#bm_bool CFSG.KD.PktBind mono1 (CFSG.KC.BM.Pkt.monoOK (CFSG.KC.BM.Pkt.lineOf CH S 23) (CFSG.KC.BM.nthN CFSG.KC.BM.Dyadic.G1.b0 0))
#bm_bool CFSG.KD.PktBind mono2 (CFSG.KC.BM.Pkt.monoOK (CFSG.KC.BM.Pkt.lineOf CH S 24) (CFSG.KC.BM.nthN CFSG.KC.BM.Dyadic.G2.b0 0))
#bm_bool CFSG.KD.PktBind mono3 (CFSG.KC.BM.Pkt.monoOK (CFSG.KC.BM.Pkt.lineOf CH S 25) (CFSG.KC.BM.nthN CFSG.KC.BM.Dyadic.G3.b0 0))
#bm_bool CFSG.KD.PktBind mono4 (CFSG.KC.BM.Pkt.monoOK (CFSG.KC.BM.Pkt.lineOf CH S 26) (CFSG.KC.BM.nthN CFSG.KC.BM.Dyadic.G4.b0 0))
#bm_bool CFSG.KD.PktBind mono5 (CFSG.KC.BM.Pkt.monoOK (CFSG.KC.BM.Pkt.lineOf CH S 27) (CFSG.KC.BM.nthN CFSG.KC.BM.Dyadic.G5.b0 0))
#bm_bool CFSG.KD.PktBind mono6 (CFSG.KC.BM.Pkt.monoOK (CFSG.KC.BM.Pkt.lineOf CH S 28) (CFSG.KC.BM.nthN CFSG.KC.BM.Dyadic.G6.b0 0))
#bm_bool CFSG.KD.PktBind mono7 (CFSG.KC.BM.Pkt.monoOK (CFSG.KC.BM.Pkt.lineOf CH S 29) (CFSG.KC.BM.nthN CFSG.KC.BM.Dyadic.G7.b0 0))
#bm_bool CFSG.KD.PktBind mono8 (CFSG.KC.BM.Pkt.monoOK (CFSG.KC.BM.Pkt.lineOf CH S 30) (CFSG.KC.BM.nthN CFSG.KC.BM.Dyadic.G8.b0 0))
#bm_bool CFSG.KD.PktBind mono9 (CFSG.KC.BM.Pkt.monoOK (CFSG.KC.BM.Pkt.lineOf CH S 31) (CFSG.KC.BM.nthN CFSG.KC.BM.Dyadic.G9.b0 0))
#bm_bool CFSG.KD.PktBind mono10 (CFSG.KC.BM.Pkt.monoOK (CFSG.KC.BM.Pkt.lineOf CH S 32) (CFSG.KC.BM.nthN CFSG.KC.BM.Dyadic.G10.b0 0))
#bm_bool CFSG.KD.PktBind mono11 (CFSG.KC.BM.Pkt.monoOK (CFSG.KC.BM.Pkt.lineOf CH S 33) (CFSG.KC.BM.nthN CFSG.KC.BM.Dyadic.G11.b0 0))
#bm_bool CFSG.KD.PktBind mono12 (CFSG.KC.BM.Pkt.monoOK (CFSG.KC.BM.Pkt.lineOf CH S 34) (CFSG.KC.BM.nthN CFSG.KC.BM.Dyadic.G12.b0 0))
#bm_bool CFSG.KD.PktBind mono13 (CFSG.KC.BM.Pkt.monoOK (CFSG.KC.BM.Pkt.lineOf CH S 35) (CFSG.KC.BM.nthN CFSG.KC.BM.Dyadic.G13.b0 0))
#bm_bool CFSG.KD.PktBind mono14 (CFSG.KC.BM.Pkt.monoOK (CFSG.KC.BM.Pkt.lineOf CH S 36) (CFSG.KC.BM.nthN CFSG.KC.BM.Dyadic.G14.b0 0))
#bm_bool CFSG.KD.PktBind mono15 (CFSG.KC.BM.Pkt.monoOK (CFSG.KC.BM.Pkt.lineOf CH S 37) (CFSG.KC.BM.nthN CFSG.KC.BM.Dyadic.G15.b0 0))
#bm_bool CFSG.KD.PktBind mono16 (CFSG.KC.BM.Pkt.monoOK (CFSG.KC.BM.Pkt.lineOf CH S 38) (CFSG.KC.BM.nthN CFSG.KC.BM.Dyadic.G16.b0 0))
#bm_bool CFSG.KD.PktBind mono17 (CFSG.KC.BM.Pkt.monoOK (CFSG.KC.BM.Pkt.lineOf CH S 39) (CFSG.KC.BM.nthN CFSG.KC.BM.Dyadic.G17.b0 0))
#bm_bool CFSG.KD.PktBind mono18 (CFSG.KC.BM.Pkt.monoOK (CFSG.KC.BM.Pkt.lineOf CH S 40) (CFSG.KC.BM.nthN CFSG.KC.BM.Dyadic.G18.b0 0))
#bm_bool CFSG.KD.PktBind mono19 (CFSG.KC.BM.Pkt.monoOK (CFSG.KC.BM.Pkt.lineOf CH S 41) (CFSG.KC.BM.nthN CFSG.KC.BM.Dyadic.G19.b0 0))
#bm_bool CFSG.KD.PktBind mono20 (CFSG.KC.BM.Pkt.monoOK (CFSG.KC.BM.Pkt.lineOf CH S 42) (CFSG.KC.BM.nthN CFSG.KC.BM.Dyadic.G20.b0 0))
#bm_bool CFSG.KD.PktBind mono21 (CFSG.KC.BM.Pkt.monoOK (CFSG.KC.BM.Pkt.lineOf CH S 43) (CFSG.KC.BM.nthN CFSG.KC.BM.Dyadic.G21.b0 0))
#bm_bool CFSG.KD.PktBind mono22 (CFSG.KC.BM.Pkt.monoOK (CFSG.KC.BM.Pkt.lineOf CH S 44) (CFSG.KC.BM.nthN CFSG.KC.BM.Dyadic.G22.b0 0))
#bm_bool CFSG.KD.PktBind mono23 (CFSG.KC.BM.Pkt.monoOK (CFSG.KC.BM.Pkt.lineOf CH S 45) (CFSG.KC.BM.nthN CFSG.KC.BM.Dyadic.G23.b0 0))
