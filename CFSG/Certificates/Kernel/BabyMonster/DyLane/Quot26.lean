module

import CFSG.Certificates.Kernel.BabyMonster.Load
import CFSG.Certificates.Kernel.BabyMonster.LoadRange
public import CFSG.Certificates.Kernel.BabyMonster.Native.DyLaneQ
public import CFSG.Certificates.Kernel.BabyMonster.DyLane.C26
public import CFSG.Certificates.Kernel.BabyMonster.FixedLine.Extra
public import CFSG.Certificates.Kernel.BabyMonster.NativePair.Data3
public import CFSG.Certificates.Kernel.BabyMonster.LatCheck

set_option maxRecDepth 100000

#bm_bool CFSG.KC.BM.DyLane lens26 (CFSG.KC.BM.andB (Nat.beq (CFSG.KC.BM.lenLL C26.rows) 69) (Nat.beq (CFSG.KC.BM.lenLL CFSG.KC.BM.NativePair.F0.rows) 69))
#bm_range CFSG.KC.BM.DyLane quot26_ 0 69 (CFSG.KC.BM.lnQuot CFSG.KC.BM.FixedLine.f C26.rows CFSG.KC.BM.NativePair.F0.rows)
