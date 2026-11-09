module

import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Bounds.CJSuz2.Data.OkT
public import CFSG.Certificates.Kernel.Common.LabM
import CFSG.Certificates.Kernel.Common.NatItems
import CFSG.Certificates.Kernel.Common.Repo

#kc_repo #kc_nat_items CFSG.KD.CJSuz2T "CFSG/Certificates/Kernel/Bounds/CJSuz2/T/data/cone_mask.items" 119435 15338662612939430622
    (MK 0 4569)
#kc_select CFSG.KD.CJSuz2T MKs MK 4569

public section

namespace CFSG.KD.CJSuz2T

open CFSG.KC CFSG.KC.LceSeg

@[expose] noncomputable def MBC (i : Nat) : Nat :=
  Nat.land (Nat.shiftRight (MKs (Nat.shiftRight i (nat_lit 8)))
    (Nat.add (nat_lit 16) (Nat.land i (nat_lit 255)))) (nat_lit 1)

@[expose] noncomputable def MB (i : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (MBC i) (nat_lit 2) (Nat.blt i (nat_lit 720479))

theorem MB_low (i : Nat) (hi : MB i = 2) : ∀ h < i, 0 < MB h := by
  intro h hh
  unfold MB at hi ⊢
  cases hb : Nat.blt i 720479
  · rw [hb] at hi
    change MBC i = 2 at hi
    have h21 : (2 : Nat) ≤ 1 := hi ▸ Nat.and_le_right
    omega
  · rw [Nat.blt_eq] at hb
    have hh' : Nat.blt h 720479 = true := by
      rw [Nat.blt_eq]
      omega
    rw [hh']
    change 0 < 2
    decide

@[expose] noncomputable def okLM (i : Nat) : Bool :=
  slOK (LabM.runLabM selWT LB MB HS) JF loF accL i

@[expose] noncomputable def okM (i : Nat) : Bool :=
  slOK (LabM.runLabCM selWT codeT MB HS) JF loF accL i

@[expose] noncomputable def okYM : Bool :=
  LabM.readsM MB (nat_lit 2048) (LceS.wLen (selWT (CY (nat_lit 1))))
    (LceS.wLen (selWT (CY (nat_lit 1)))) (CY (nat_lit 2))

end CFSG.KD.CJSuz2T

end
