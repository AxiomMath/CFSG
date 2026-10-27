module

public import CFSG.Certificates.Kernel.Bounds.HNAlt.DceSP
public import CFSG.Certificates.Kernel.Bounds.HNAlt.Data.Disp
public import CFSG.Certificates.Kernel.Bounds.Core3
public import Certificates.Data.Kernel.LceSSeg
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.EachUnfoldKeyed

public section

#kc_repo #kc_items_root CFSG.KD.HNA.ES_0.J "CFSG/Certificates/Kernel/Bounds/HNAlt/Data/tab/ES_0_J.bin" 60822 1445135086289482725
#kc_repo #kc_items_root CFSG.KD.HNA.ES_0.lo "CFSG/Certificates/Kernel/Bounds/HNAlt/Data/tab/ES_0_lo.bin" 429 14533142043532364754
#kc_repo #kc_items_root CFSG.KD.HNA.ES_0.acc "CFSG/Certificates/Kernel/Bounds/HNAlt/Data/tab/ES_0_acc.bin" 644 13958687986637284968
#kc_repo #kc_items_root CFSG.KD.HNA.ES_0.fin "CFSG/Certificates/Kernel/Bounds/HNAlt/Data/tab/ES_0_fin.bin" 4080 16015002596854717002
#kc_repo #kc_items_root CFSG.KD.HNA.ES_0.key "CFSG/Certificates/Kernel/Bounds/HNAlt/Data/tab/ES_0_key.bin" 429 10154328578080140169
#kc_repo #kc_items_root CFSG.KD.HNA.ES_0.nkey "CFSG/Certificates/Kernel/Bounds/HNAlt/Data/tab/ES_0_n_key.bin" 400 12949466676696320082
#kc_repo #kc_items_root CFSG.KD.HNA.ES_0.nv "CFSG/Certificates/Kernel/Bounds/HNAlt/Data/tab/ES_0_n_v.bin" 3840 12319937239989309073

namespace CFSG.KD.HNA.ES_0

open CFSG.KD.HNA CFSG.KC.HNA.DceS CFSG.KC.LceSeg

@[expose] noncomputable def ok (t : Nat) : Bool :=
  Nat.beq (runSorted (mat (Ed (key t))) (nat_lit 19)
      (bits MD (Nat.mul (nat_lit 24) (key t)) (nat_lit 24))
      (seg J (lo (t + 1) - lo t) (lo t)) (acc t))
    (fin t)

@[expose] noncomputable def okn (t : Nat) : Bool :=
  Nat.beq (sortedCount (nv t)) (bits MD (Nat.mul (nat_lit 24) (nkey t)) (nat_lit 24))

end CFSG.KD.HNA.ES_0

#kc_each_unfold_keyed CFSG.KD.HNA.ES_0.ok 0 85 as CFSG.KD.HNA.es key CFSG.KD.HNA.ES_0.key
  eval CFSG.KD.HNA.ES_0.lo CFSG.KD.HNA.ES_0.acc CFSG.KD.HNA.ES_0.fin CFSG.KD.HNA.ES_0.key

#kc_each_unfold_keyed CFSG.KD.HNA.ES_0.okn 0 80 as CFSG.KD.HNA.es key CFSG.KD.HNA.ES_0.nkey sfx n
  eval CFSG.KD.HNA.ES_0.nv CFSG.KD.HNA.ES_0.nkey

end
