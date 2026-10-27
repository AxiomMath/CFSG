module

import CFSG.Certificates.Kernel.BabyMonster.Load
import CFSG.Certificates.Kernel.BabyMonster.LoadRange
public import CFSG.Certificates.Kernel.BabyMonster.Native.DyLane
public import CFSG.Certificates.Kernel.BabyMonster.Dyadic.Basis
public import CFSG.Certificates.Kernel.BabyMonster.DyLane.Strips
public import CFSG.Certificates.Kernel.BabyMonster.DyLane.Masks

set_option maxRecDepth 100000

#bm_bool CFSG.KC.BM.Dyadic lnSSLen (Nat.beq (CFSG.KC.BM.lenLL SS) 274)
#bm_bool CFSG.KC.BM.Dyadic lnKKOK (CFSG.KC.BM.lnEqLL KK CFSG.KC.BM.lnKK)
#bm_range CFSG.KC.BM.Dyadic lnStrip 0 274 (CFSG.KC.BM.lnStripOK Bs SS)
