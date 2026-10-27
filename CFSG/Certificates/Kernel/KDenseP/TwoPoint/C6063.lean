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

#kc_plan CFSG.KD.TP.c6063 "c6063.plan.txt" 459740 14339346813226665241
#kc_plan CFSG.KD.TP.c6063 "c6063.grp.txt" 2327 8780125984281915181
#kc_repo #kc_natBin CFSG.KD.TP.c6063 RX0 "CFSG/Certificates/Kernel/KDenseP/TwoPoint/c6063_rec/RX0.bin" 63699 11563375030640710472
#kc_repo #kc_natBin CFSG.KD.TP.c6063 RW0 "CFSG/Certificates/Kernel/KDenseP/TwoPoint/c6063_rec/RW0.bin" 65515 16869023809305344148
#kc_repo #kc_natBin CFSG.KD.TP.c6063 RX1 "CFSG/Certificates/Kernel/KDenseP/TwoPoint/c6063_rec/RX1.bin" 63703 2303506747891739413
#kc_repo #kc_natBin CFSG.KD.TP.c6063 RW1 "CFSG/Certificates/Kernel/KDenseP/TwoPoint/c6063_rec/RW1.bin" 65535 3738003341951785530
#kc_repo #kc_natBin CFSG.KD.TP.c6063 RX2 "CFSG/Certificates/Kernel/KDenseP/TwoPoint/c6063_rec/RX2.bin" 63707 4329520881696180292
#kc_repo #kc_natBin CFSG.KD.TP.c6063 RW2 "CFSG/Certificates/Kernel/KDenseP/TwoPoint/c6063_rec/RW2.bin" 65535 17336453181276738979
#kc_repo #kc_natBin CFSG.KD.TP.c6063 RX3 "CFSG/Certificates/Kernel/KDenseP/TwoPoint/c6063_rec/RX3.bin" 63707 17163279456499091116
#kc_repo #kc_natBin CFSG.KD.TP.c6063 RW3 "CFSG/Certificates/Kernel/KDenseP/TwoPoint/c6063_rec/RW3.bin" 65535 17622798455249754581
#kc_repo #kc_natBin CFSG.KD.TP.c6063 RX4 "CFSG/Certificates/Kernel/KDenseP/TwoPoint/c6063_rec/RX4.bin" 63707 11585826869782799613
#kc_repo #kc_natBin CFSG.KD.TP.c6063 RW4 "CFSG/Certificates/Kernel/KDenseP/TwoPoint/c6063_rec/RW4.bin" 65535 17235012962831945732
#kc_repo #kc_natBin CFSG.KD.TP.c6063 RX5 "CFSG/Certificates/Kernel/KDenseP/TwoPoint/c6063_rec/RX5.bin" 63707 4986524133586109984
#kc_repo #kc_natBin CFSG.KD.TP.c6063 RW5 "CFSG/Certificates/Kernel/KDenseP/TwoPoint/c6063_rec/RW5.bin" 65531 12164219337160798167
#kc_repo #kc_natBin CFSG.KD.TP.c6063 RX6 "CFSG/Certificates/Kernel/KDenseP/TwoPoint/c6063_rec/RX6.bin" 63707 11598527179959888452
#kc_repo #kc_natBin CFSG.KD.TP.c6063 RW6 "CFSG/Certificates/Kernel/KDenseP/TwoPoint/c6063_rec/RW6.bin" 65535 14535064690704186768
#kc_repo #kc_natBin CFSG.KD.TP.c6063 RX7 "CFSG/Certificates/Kernel/KDenseP/TwoPoint/c6063_rec/RX7.bin" 63703 62961006345073929
#kc_repo #kc_natBin CFSG.KD.TP.c6063 RW7 "CFSG/Certificates/Kernel/KDenseP/TwoPoint/c6063_rec/RW7.bin" 65535 14471561213470934866
#kc_repo #kc_natBin CFSG.KD.TP.c6063 RX8 "CFSG/Certificates/Kernel/KDenseP/TwoPoint/c6063_rec/RX8.bin" 63707 14833375369191692931
#kc_repo #kc_natBin CFSG.KD.TP.c6063 RW8 "CFSG/Certificates/Kernel/KDenseP/TwoPoint/c6063_rec/RW8.bin" 65527 6832168893557554810
#kc_repo #kc_natBin CFSG.KD.TP.c6063 RX9 "CFSG/Certificates/Kernel/KDenseP/TwoPoint/c6063_rec/RX9.bin" 63707 10088010414753118267
#kc_repo #kc_natBin CFSG.KD.TP.c6063 RW9 "CFSG/Certificates/Kernel/KDenseP/TwoPoint/c6063_rec/RW9.bin" 65535 11692246674657419261
#kc_repo #kc_natBin CFSG.KD.TP.c6063 RX10 "CFSG/Certificates/Kernel/KDenseP/TwoPoint/c6063_rec/RX10.bin" 63691 9223738135650518130
#kc_repo #kc_natBin CFSG.KD.TP.c6063 RW10 "CFSG/Certificates/Kernel/KDenseP/TwoPoint/c6063_rec/RW10.bin" 65531 5453030490653566768
#kc_repo #kc_natBin CFSG.KD.TP.c6063 RX11 "CFSG/Certificates/Kernel/KDenseP/TwoPoint/c6063_rec/RX11.bin" 63703 4028971612659029614
#kc_repo #kc_natBin CFSG.KD.TP.c6063 RW11 "CFSG/Certificates/Kernel/KDenseP/TwoPoint/c6063_rec/RW11.bin" 65535 8368766730364975864
#kc_repo #kc_natBin CFSG.KD.TP.c6063 RX12 "CFSG/Certificates/Kernel/KDenseP/TwoPoint/c6063_rec/RX12.bin" 63707 4241496256276956973
#kc_repo #kc_natBin CFSG.KD.TP.c6063 RW12 "CFSG/Certificates/Kernel/KDenseP/TwoPoint/c6063_rec/RW12.bin" 65534 9351758653005394266
#kc_repo #kc_natBin CFSG.KD.TP.c6063 RX13 "CFSG/Certificates/Kernel/KDenseP/TwoPoint/c6063_rec/RX13.bin" 63707 2355809797475026070
#kc_repo #kc_natBin CFSG.KD.TP.c6063 RW13 "CFSG/Certificates/Kernel/KDenseP/TwoPoint/c6063_rec/RW13.bin" 65535 17936981298269132013
#kc_plan CFSG.KD.TP.c6063 "c6063.rec.txt" 13513 6465815467558446662
#kc_select CFSG.KD.TP.c6063 CH CH 101
#kc_select CFSG.KD.TP.c6063 IXf IX 366
#kc_select CFSG.KD.TP.c6063 PRf PR 89
#kc_select CFSG.KD.TP.c6063 GKf GK 101
#kc_select CFSG.KD.TP.c6063 RXf RX 14
#kc_select CFSG.KD.TP.c6063 RAf RA 14
#kc_select CFSG.KD.TP.c6063 RWf RW 14
#kc_listDispatch CFSG.KD.TP.c6063 WD wd 16
#kc_listDispatch CFSG.KD.TP.c6063 Gf G 18

namespace CFSG.KD.TP.c6063

open CFSG.KC.KDense

@[expose] noncomputable def WL (σ : Nat) : List CFSG.Monster.AxisCount.Native.Gen :=
  CFSG.KC.KDenseP.decW (WD σ)

@[expose] noncomputable def S0 (k : Nat) : St :=
  Bool.rec (motive := fun _ => St) ((fun j => mkSt (RXf j) (RAf j) (RWf j)) (Nat.sub k 3))
    (Bool.rec (motive := fun _ => St) (mkSt I0X I0A I0W) (mkSt I1X I1A I1W)
      (Nat.beq k 1)) (Nat.blt k 3)

@[expose] noncomputable def rn (c : Nat) (s : St) : St := CFSG.KD.TP.run (WD (f20 c (nat_lit 0))) c s

@[expose] noncomputable def CHI (k : Nat) : Nat := CH (IXf k)

end CFSG.KD.TP.c6063

end
