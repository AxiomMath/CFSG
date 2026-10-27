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

#kc_plan CFSG.KD.TP.c6072 "c6072.plan.txt" 86397 9494770463618356596
#kc_plan CFSG.KD.TP.c6072 "c6072.grp.txt" 2799 17062345538166966930
#kc_repo #kc_natBin CFSG.KD.TP.c6072 RX0 "CFSG/Certificates/Kernel/KDenseP/TwoPoint/c6072_rec/RX0.bin" 63707 12877989315777160621
#kc_repo #kc_natBin CFSG.KD.TP.c6072 RW0 "CFSG/Certificates/Kernel/KDenseP/TwoPoint/c6072_rec/RW0.bin" 65535 4526109382035183924
#kc_repo #kc_natBin CFSG.KD.TP.c6072 RX1 "CFSG/Certificates/Kernel/KDenseP/TwoPoint/c6072_rec/RX1.bin" 63699 6371817829427656489
#kc_repo #kc_natBin CFSG.KD.TP.c6072 RW1 "CFSG/Certificates/Kernel/KDenseP/TwoPoint/c6072_rec/RW1.bin" 65535 3123768631694141036
#kc_repo #kc_natBin CFSG.KD.TP.c6072 RX2 "CFSG/Certificates/Kernel/KDenseP/TwoPoint/c6072_rec/RX2.bin" 63703 15061408896407185687
#kc_repo #kc_natBin CFSG.KD.TP.c6072 RW2 "CFSG/Certificates/Kernel/KDenseP/TwoPoint/c6072_rec/RW2.bin" 65535 6240582985696308904
#kc_repo #kc_natBin CFSG.KD.TP.c6072 RX3 "CFSG/Certificates/Kernel/KDenseP/TwoPoint/c6072_rec/RX3.bin" 63695 9260836967576025986
#kc_repo #kc_natBin CFSG.KD.TP.c6072 RW3 "CFSG/Certificates/Kernel/KDenseP/TwoPoint/c6072_rec/RW3.bin" 65531 16249153101377137796
#kc_repo #kc_natBin CFSG.KD.TP.c6072 RX4 "CFSG/Certificates/Kernel/KDenseP/TwoPoint/c6072_rec/RX4.bin" 63703 11616048302769177248
#kc_repo #kc_natBin CFSG.KD.TP.c6072 RW4 "CFSG/Certificates/Kernel/KDenseP/TwoPoint/c6072_rec/RW4.bin" 65535 18352024816752968898
#kc_repo #kc_natBin CFSG.KD.TP.c6072 RX5 "CFSG/Certificates/Kernel/KDenseP/TwoPoint/c6072_rec/RX5.bin" 63703 2281355642978768159
#kc_repo #kc_natBin CFSG.KD.TP.c6072 RW5 "CFSG/Certificates/Kernel/KDenseP/TwoPoint/c6072_rec/RW5.bin" 65535 15592246598604248243
#kc_repo #kc_natBin CFSG.KD.TP.c6072 RX6 "CFSG/Certificates/Kernel/KDenseP/TwoPoint/c6072_rec/RX6.bin" 63699 14654347441021499125
#kc_repo #kc_natBin CFSG.KD.TP.c6072 RW6 "CFSG/Certificates/Kernel/KDenseP/TwoPoint/c6072_rec/RW6.bin" 65535 11904323560347196585
#kc_repo #kc_natBin CFSG.KD.TP.c6072 RX7 "CFSG/Certificates/Kernel/KDenseP/TwoPoint/c6072_rec/RX7.bin" 63703 6943155675352119386
#kc_repo #kc_natBin CFSG.KD.TP.c6072 RW7 "CFSG/Certificates/Kernel/KDenseP/TwoPoint/c6072_rec/RW7.bin" 65535 7266051957924402515
#kc_repo #kc_natBin CFSG.KD.TP.c6072 RX8 "CFSG/Certificates/Kernel/KDenseP/TwoPoint/c6072_rec/RX8.bin" 63707 12403261186192770936
#kc_repo #kc_natBin CFSG.KD.TP.c6072 RW8 "CFSG/Certificates/Kernel/KDenseP/TwoPoint/c6072_rec/RW8.bin" 65535 9584172118237511314
#kc_repo #kc_natBin CFSG.KD.TP.c6072 RX9 "CFSG/Certificates/Kernel/KDenseP/TwoPoint/c6072_rec/RX9.bin" 63699 11325412984236148130
#kc_repo #kc_natBin CFSG.KD.TP.c6072 RW9 "CFSG/Certificates/Kernel/KDenseP/TwoPoint/c6072_rec/RW9.bin" 65535 4087918179198453841
#kc_repo #kc_natBin CFSG.KD.TP.c6072 RX10 "CFSG/Certificates/Kernel/KDenseP/TwoPoint/c6072_rec/RX10.bin" 63703 15509150636802020164
#kc_repo #kc_natBin CFSG.KD.TP.c6072 RW10 "CFSG/Certificates/Kernel/KDenseP/TwoPoint/c6072_rec/RW10.bin" 65535 10571964929298620652
#kc_repo #kc_natBin CFSG.KD.TP.c6072 RX11 "CFSG/Certificates/Kernel/KDenseP/TwoPoint/c6072_rec/RX11.bin" 63707 3803227447521117725
#kc_repo #kc_natBin CFSG.KD.TP.c6072 RW11 "CFSG/Certificates/Kernel/KDenseP/TwoPoint/c6072_rec/RW11.bin" 65535 13170021407332651013
#kc_repo #kc_natBin CFSG.KD.TP.c6072 RX12 "CFSG/Certificates/Kernel/KDenseP/TwoPoint/c6072_rec/RX12.bin" 63707 13226787809133183037
#kc_repo #kc_natBin CFSG.KD.TP.c6072 RW12 "CFSG/Certificates/Kernel/KDenseP/TwoPoint/c6072_rec/RW12.bin" 65535 15451098978283594830
#kc_repo #kc_natBin CFSG.KD.TP.c6072 RX13 "CFSG/Certificates/Kernel/KDenseP/TwoPoint/c6072_rec/RX13.bin" 63707 11985516742884029624
#kc_repo #kc_natBin CFSG.KD.TP.c6072 RW13 "CFSG/Certificates/Kernel/KDenseP/TwoPoint/c6072_rec/RW13.bin" 65534 16905417224665898910
#kc_repo #kc_natBin CFSG.KD.TP.c6072 RX14 "CFSG/Certificates/Kernel/KDenseP/TwoPoint/c6072_rec/RX14.bin" 63707 15495288537311843912
#kc_repo #kc_natBin CFSG.KD.TP.c6072 RW14 "CFSG/Certificates/Kernel/KDenseP/TwoPoint/c6072_rec/RW14.bin" 65535 11652774254899159895
#kc_repo #kc_natBin CFSG.KD.TP.c6072 RX15 "CFSG/Certificates/Kernel/KDenseP/TwoPoint/c6072_rec/RX15.bin" 63707 5817192262850805466
#kc_repo #kc_natBin CFSG.KD.TP.c6072 RW15 "CFSG/Certificates/Kernel/KDenseP/TwoPoint/c6072_rec/RW15.bin" 65535 13749885473509289417
#kc_repo #kc_natBin CFSG.KD.TP.c6072 RX16 "CFSG/Certificates/Kernel/KDenseP/TwoPoint/c6072_rec/RX16.bin" 63703 11882063840418904601
#kc_repo #kc_natBin CFSG.KD.TP.c6072 RW16 "CFSG/Certificates/Kernel/KDenseP/TwoPoint/c6072_rec/RW16.bin" 65535 5743093758759376246
#kc_repo #kc_natBin CFSG.KD.TP.c6072 RX17 "CFSG/Certificates/Kernel/KDenseP/TwoPoint/c6072_rec/RX17.bin" 63707 2027468724879383622
#kc_repo #kc_natBin CFSG.KD.TP.c6072 RW17 "CFSG/Certificates/Kernel/KDenseP/TwoPoint/c6072_rec/RW17.bin" 65535 11080259497956486228
#kc_repo #kc_natBin CFSG.KD.TP.c6072 RX18 "CFSG/Certificates/Kernel/KDenseP/TwoPoint/c6072_rec/RX18.bin" 63699 15089261245429273690
#kc_repo #kc_natBin CFSG.KD.TP.c6072 RW18 "CFSG/Certificates/Kernel/KDenseP/TwoPoint/c6072_rec/RW18.bin" 65535 15455597623196226053
#kc_repo #kc_natBin CFSG.KD.TP.c6072 RX19 "CFSG/Certificates/Kernel/KDenseP/TwoPoint/c6072_rec/RX19.bin" 63703 1579704390708551488
#kc_repo #kc_natBin CFSG.KD.TP.c6072 RW19 "CFSG/Certificates/Kernel/KDenseP/TwoPoint/c6072_rec/RW19.bin" 65535 8594448896015128397
#kc_repo #kc_natBin CFSG.KD.TP.c6072 RX20 "CFSG/Certificates/Kernel/KDenseP/TwoPoint/c6072_rec/RX20.bin" 63707 14929372224676786267
#kc_repo #kc_natBin CFSG.KD.TP.c6072 RW20 "CFSG/Certificates/Kernel/KDenseP/TwoPoint/c6072_rec/RW20.bin" 65535 4609946785326516856
#kc_plan CFSG.KD.TP.c6072 "c6072.rec.txt" 20274 15465873975206313564
#kc_select CFSG.KD.TP.c6072 CH CH 117
#kc_select CFSG.KD.TP.c6072 IXf IX 117
#kc_select CFSG.KD.TP.c6072 PRf PR 113
#kc_select CFSG.KD.TP.c6072 GKf GK 117
#kc_listDispatch CFSG.KD.TP.c6072 WD wd 6
#kc_listDispatch CFSG.KD.TP.c6072 Gf G 21
#kc_select CFSG.KD.TP.c6072 RXf RX 21
#kc_select CFSG.KD.TP.c6072 RAf RA 21
#kc_select CFSG.KD.TP.c6072 RWf RW 21

namespace CFSG.KD.TP.c6072

open CFSG.KC.KDense

@[expose] noncomputable def WL (σ : Nat) : List CFSG.Monster.AxisCount.Native.Gen :=
  CFSG.KC.KDenseP.decW (WD σ)

@[expose] noncomputable def S0 (k : Nat) : St :=
  Bool.rec (motive := fun _ => St) ((fun j => mkSt (RXf j) (RAf j) (RWf j)) (Nat.sub k 3))
    (CFSG.KD.KDF.I k) (Nat.blt k 3)

@[expose] noncomputable def rn (c : Nat) (s : St) : St := CFSG.KD.TP.run (WD (f20 c (nat_lit 0))) c s

@[expose] noncomputable def CHI (k : Nat) : Nat := CH (IXf k)

end CFSG.KD.TP.c6072

end
