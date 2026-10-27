module

public import CFSG.Certificates.Kernel.BabyMonster.LatBind.Text0
public import CFSG.Certificates.Kernel.BabyMonster.LatBind.Text1
public import CFSG.Certificates.Kernel.BabyMonster.LatBind.Text2
public import CFSG.Certificates.Kernel.BabyMonster.LatBind.Text3
public import CFSG.Certificates.Kernel.BabyMonster.LatBind.Text4
public import CFSG.Certificates.Kernel.BabyMonster.LatBind.Text5
public import CFSG.Certificates.Kernel.BabyMonster.LatBind.Text6
public import CFSG.Certificates.Kernel.BabyMonster.LatBind.Text7
public import CFSG.Certificates.Kernel.BabyMonster.LatBind.Text8
public import CFSG.Certificates.Kernel.BabyMonster.LatBind.Text9
public import CFSG.Certificates.Kernel.BabyMonster.LatBind.Text10
public import CFSG.Certificates.Kernel.BabyMonster.TBind.Chunks

public section

namespace CFSG.KD.LatBind

open CFSG.KD.TBind

@[expose] noncomputable def CH : List (Nat × Nat) :=
  appP C0.CH (appP C1.CH (appP C2.CH (appP C3.CH (appP C4.CH (appP C5.CH (appP C6.CH (appP C7.CH (appP C8.CH (appP C9.CH C10.CH)))))))))

end CFSG.KD.LatBind

end
