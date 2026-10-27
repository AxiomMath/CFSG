module

public import CFSG.Certificates.Kernel.Bounds.HNAlt.DceSP
public import CFSG.Certificates.Kernel.Bounds.HNAlt.Data.Disp
public import CFSG.Certificates.Kernel.Bounds.Core3
public import Certificates.Data.Kernel.LceSSeg
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.EachUnfoldKeyed

public section

#kc_repo #kc_items_root CFSG.KD.HNA.S_0.J "CFSG/Certificates/Kernel/Bounds/HNAlt/Data/tab/S_0_J.bin" 76554 11115256447485258470
#kc_repo #kc_items_root CFSG.KD.HNA.S_0.lo "CFSG/Certificates/Kernel/Bounds/HNAlt/Data/tab/S_0_lo.bin" 259 8364949276928630711
#kc_repo #kc_items_root CFSG.KD.HNA.S_0.acc "CFSG/Certificates/Kernel/Bounds/HNAlt/Data/tab/S_0_acc.bin" 264 15452635126280179273
#kc_repo #kc_items_root CFSG.KD.HNA.S_0.fin "CFSG/Certificates/Kernel/Bounds/HNAlt/Data/tab/S_0_fin.bin" 214 15328208412500246251
#kc_repo #kc_items_root CFSG.KD.HNA.S_0.key "CFSG/Certificates/Kernel/Bounds/HNAlt/Data/tab/S_0_key.bin" 259 9651290238153698721
#kc_repo #kc_items_root CFSG.KD.HNA.S_0.ekey "CFSG/Certificates/Kernel/Bounds/HNAlt/Data/tab/S_0_e_key.bin" 170 12370044748841425944

namespace CFSG.KD.HNA.S_0

open CFSG.KD.HNA CFSG.KC.HNA.DceS CFSG.KC.LceSeg

@[expose] noncomputable def ok (t : Nat) : Bool :=
  Nat.beq (runStab FB (Ed (key t)) (nat_lit 5) (nat_lit 708) NF (key t) (SGd (key t))
      (seg J (lo (t + 1) - lo t) (lo t)) (acc t))
    (Bool.rec (motive := fun _ => Nat)
      (Nat.succ (bits MD (Nat.mul (nat_lit 24) (key t)) (nat_lit 24))) (fin t)
      (Nat.beq (key (t + 1)) (key t)))

@[expose] noncomputable def oke (t : Nat) : Bool :=
  Nat.beq (bits MD (Nat.mul (nat_lit 24) (ekey t)) (nat_lit 24)) (nat_lit 1)

end CFSG.KD.HNA.S_0

#kc_each_unfold_keyed CFSG.KD.HNA.S_0.ok 0 51 as CFSG.KD.HNA.s key CFSG.KD.HNA.S_0.key
  eval CFSG.KD.HNA.S_0.lo CFSG.KD.HNA.S_0.acc CFSG.KD.HNA.S_0.fin CFSG.KD.HNA.S_0.key

#kc_each_unfold_keyed CFSG.KD.HNA.S_0.oke 0 34 as CFSG.KD.HNA.s key CFSG.KD.HNA.S_0.ekey sfx e
  eval CFSG.KD.HNA.S_0.ekey

end
