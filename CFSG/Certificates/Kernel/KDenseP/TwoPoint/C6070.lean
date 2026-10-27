module

import CFSG.Certificates.Kernel.Common.Repo
public import CFSG.Certificates.Kernel.KDenseP.TwoPoint.MonoTab
public import CFSG.Certificates.Kernel.KDenseP.TwoPoint.Pairs
public import Certificates.Data.Kernel.KDenseP.Words
public import CFSG.Certificates.Kernel.KDense.Data.Fix
public import CFSG.Certificates.Kernel.KDenseP.TwoPoint.Run
public import Certificates.Data.Kernel.KDenseP.Replay
public import CFSG.Certificates.Kernel.Common.Plan
public import CFSG.Certificates.Kernel.KDense.Y443.Pairs
public import CFSG.Monster.AxisCount.CoverLetters
public import CFSG.Monster.B.TwoA.Base.Flags
public import CFSG.Monster.B.TwoA.Base.Par45A
public import CFSG.Monster.B.TwoA.Par3.Main
public import CFSG.Monster.B.TwoA.Par3.MainBase
public import CFSG.Monster.B.TwoA.Sp8.GenActionHom
public import CFSG.Monster.Existence.ELevelBasic
public import CFSG.Monster.Existence.TwoPoint.Fi23ConjBase
public import CFSG.Monster.Existence.TwoPoint.Fi23MiscBase
public import CFSG.Monster.Existence.TwoPoint.Fi23Rels0Base
public import CFSG.Monster.Existence.TwoPoint.Fi23Rels1Base
public import CFSG.Monster.Existence.TwoPoint.Fi23Rels2Base
public import CFSG.Monster.Existence.TwoPoint.Fi23Rels3Base
public import CFSG.Monster.Existence.TwoPoint.Fi23Rels4Base
public import CFSG.Monster.Existence.TwoPoint.Fi23Rels5Base
public import CFSG.Monster.Existence.TwoPoint.Fi23RelsLongADBase
public import CFSG.Monster.Existence.TwoPoint.Fi23RelsLongJBase
public import CFSG.Monster.Existence.TwoPoint.Fi23RelsLongMBase
public import CFSG.Monster.Existence.TwoPoint.Fi23RelsLongPBase
public import CFSG.Monster.Existence.TwoPoint.Fi23S4CommBase
public import CFSG.Monster.Existence.TwoPoint.Fi23S4ConjBase
public import CFSG.Monster.Existence.TwoPoint.Fi23S4CubeBase
public import CFSG.Monster.Existence.TwoPoint.GammaExclCheckBase
public import CFSG.Monster.Existence.TwoPoint.ThetaTrace
public import CFSG.Sporadic.Bridge.Fi23Surj
public import CFSG.Sporadic.Co1Base
public import CFSG.YGroups.Y443.Native.EdgeNoncommBase

public section

set_option maxRecDepth 100000

#kc_plan CFSG.KD.TP.c6070 "c6070.plan.txt" 423537 4235021072576080018
#kc_plan CFSG.KD.TP.c6070 "c6070.grp.txt" 1987 1187663504161886756
#kc_repo #kc_natBin CFSG.KD.TP.c6070 RX0 "CFSG/Certificates/Kernel/KDenseP/TwoPoint/c6070_rec/RX0.bin" 63703 1195134735530932508
#kc_repo #kc_natBin CFSG.KD.TP.c6070 RW0 "CFSG/Certificates/Kernel/KDenseP/TwoPoint/c6070_rec/RW0.bin" 65531 5859804720390657495
#kc_repo #kc_natBin CFSG.KD.TP.c6070 RX1 "CFSG/Certificates/Kernel/KDenseP/TwoPoint/c6070_rec/RX1.bin" 63695 9101336133333247015
#kc_repo #kc_natBin CFSG.KD.TP.c6070 RW1 "CFSG/Certificates/Kernel/KDenseP/TwoPoint/c6070_rec/RW1.bin" 65531 3546765214976288651
#kc_repo #kc_natBin CFSG.KD.TP.c6070 RX2 "CFSG/Certificates/Kernel/KDenseP/TwoPoint/c6070_rec/RX2.bin" 63707 12908047375354076889
#kc_repo #kc_natBin CFSG.KD.TP.c6070 RW2 "CFSG/Certificates/Kernel/KDenseP/TwoPoint/c6070_rec/RW2.bin" 65535 8846433113135113730
#kc_repo #kc_natBin CFSG.KD.TP.c6070 RX3 "CFSG/Certificates/Kernel/KDenseP/TwoPoint/c6070_rec/RX3.bin" 63703 16353942296177228805
#kc_repo #kc_natBin CFSG.KD.TP.c6070 RW3 "CFSG/Certificates/Kernel/KDenseP/TwoPoint/c6070_rec/RW3.bin" 65535 6540285009371660654
#kc_repo #kc_natBin CFSG.KD.TP.c6070 RX4 "CFSG/Certificates/Kernel/KDenseP/TwoPoint/c6070_rec/RX4.bin" 63707 9841873286938410400
#kc_repo #kc_natBin CFSG.KD.TP.c6070 RW4 "CFSG/Certificates/Kernel/KDenseP/TwoPoint/c6070_rec/RW4.bin" 65535 7056387589447568661
#kc_repo #kc_natBin CFSG.KD.TP.c6070 RX5 "CFSG/Certificates/Kernel/KDenseP/TwoPoint/c6070_rec/RX5.bin" 63707 3523143931807187905
#kc_repo #kc_natBin CFSG.KD.TP.c6070 RW5 "CFSG/Certificates/Kernel/KDenseP/TwoPoint/c6070_rec/RW5.bin" 65535 2633640689279882882
#kc_repo #kc_natBin CFSG.KD.TP.c6070 RX6 "CFSG/Certificates/Kernel/KDenseP/TwoPoint/c6070_rec/RX6.bin" 63707 9089559841160838802
#kc_repo #kc_natBin CFSG.KD.TP.c6070 RW6 "CFSG/Certificates/Kernel/KDenseP/TwoPoint/c6070_rec/RW6.bin" 65535 1351190139093928962
#kc_repo #kc_natBin CFSG.KD.TP.c6070 RX7 "CFSG/Certificates/Kernel/KDenseP/TwoPoint/c6070_rec/RX7.bin" 63707 12806776484053932124
#kc_repo #kc_natBin CFSG.KD.TP.c6070 RW7 "CFSG/Certificates/Kernel/KDenseP/TwoPoint/c6070_rec/RW7.bin" 65535 17160520573488601412
#kc_repo #kc_natBin CFSG.KD.TP.c6070 RX8 "CFSG/Certificates/Kernel/KDenseP/TwoPoint/c6070_rec/RX8.bin" 63707 13504508892072520886
#kc_repo #kc_natBin CFSG.KD.TP.c6070 RW8 "CFSG/Certificates/Kernel/KDenseP/TwoPoint/c6070_rec/RW8.bin" 65535 2899933555474834953
#kc_repo #kc_natBin CFSG.KD.TP.c6070 RX9 "CFSG/Certificates/Kernel/KDenseP/TwoPoint/c6070_rec/RX9.bin" 63707 6726007168854436951
#kc_repo #kc_natBin CFSG.KD.TP.c6070 RW9 "CFSG/Certificates/Kernel/KDenseP/TwoPoint/c6070_rec/RW9.bin" 65535 18190910353795841253
#kc_repo #kc_natBin CFSG.KD.TP.c6070 RX10 "CFSG/Certificates/Kernel/KDenseP/TwoPoint/c6070_rec/RX10.bin" 63707 12244662323344346202
#kc_repo #kc_natBin CFSG.KD.TP.c6070 RW10 "CFSG/Certificates/Kernel/KDenseP/TwoPoint/c6070_rec/RW10.bin" 65535 4729972787363797603
#kc_repo #kc_natBin CFSG.KD.TP.c6070 RX11 "CFSG/Certificates/Kernel/KDenseP/TwoPoint/c6070_rec/RX11.bin" 63703 9557268426833475879
#kc_repo #kc_natBin CFSG.KD.TP.c6070 RW11 "CFSG/Certificates/Kernel/KDenseP/TwoPoint/c6070_rec/RW11.bin" 65535 1473500179062462700
#kc_repo #kc_natBin CFSG.KD.TP.c6070 RX12 "CFSG/Certificates/Kernel/KDenseP/TwoPoint/c6070_rec/RX12.bin" 63703 8248066387183241479
#kc_repo #kc_natBin CFSG.KD.TP.c6070 RW12 "CFSG/Certificates/Kernel/KDenseP/TwoPoint/c6070_rec/RW12.bin" 65534 6534861614813809837
#kc_repo #kc_natBin CFSG.KD.TP.c6070 RX13 "CFSG/Certificates/Kernel/KDenseP/TwoPoint/c6070_rec/RX13.bin" 63703 6747246128885797178
#kc_repo #kc_natBin CFSG.KD.TP.c6070 RW13 "CFSG/Certificates/Kernel/KDenseP/TwoPoint/c6070_rec/RW13.bin" 65535 2570155405202314214
#kc_plan CFSG.KD.TP.c6070 "c6070.rec.txt" 13514 9383264522408298323
#kc_select CFSG.KD.TP.c6070 CH CH 85
#kc_select CFSG.KD.TP.c6070 IXf IX 312
#kc_select CFSG.KD.TP.c6070 PRf PR 83
#kc_select CFSG.KD.TP.c6070 GKf GK 85
#kc_select CFSG.KD.TP.c6070 RXf RX 14
#kc_select CFSG.KD.TP.c6070 RAf RA 14
#kc_select CFSG.KD.TP.c6070 RWf RW 14
#kc_listDispatch CFSG.KD.TP.c6070 WD wd 8
#kc_listDispatch CFSG.KD.TP.c6070 Gf G 16

namespace CFSG.KD.TP.c6070

open CFSG.KC.KDense

@[expose] noncomputable def WL (σ : Nat) : List CFSG.Monster.AxisCount.Native.Gen :=
  CFSG.KC.KDenseP.decW (WD σ)

@[expose] noncomputable def S0 (k : Nat) : St :=
  Bool.rec (motive := fun _ => St) ((fun j => mkSt (RXf j) (RAf j) (RWf j)) (Nat.sub k 3))
    (Bool.rec (motive := fun _ => St) (mkSt I0X I0A I0W) (mkSt I1X I1A I1W)
      (Nat.beq k 1)) (Nat.blt k 3)

@[expose] noncomputable def rn (c : Nat) (s : St) : St := CFSG.KD.TP.run (WD (f20 c (nat_lit 0))) c s

@[expose] noncomputable def CHI (k : Nat) : Nat := CH (IXf k)

end CFSG.KD.TP.c6070

end
