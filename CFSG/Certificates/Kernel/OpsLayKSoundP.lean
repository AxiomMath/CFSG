module

public import Certificates.Data.Kernel.OpsLayK
public import Certificates.Data.CFSGNative.SectionRank.Fp
import CFSG.Certificates.Kernel.OpsLayKSndP

public section

namespace CFSG.KC.OpsLayK

open CFSG.KC.LQT CFSG.SectionRank.Native

theorem secKP_sound {c : Lay} {p d A B : Nat} {LA LB : List Char} {D : SecData}
    (hc : c.ok = true) (hp : c.p = p) (hd : c.d = d)
    (hA : decOK c A LA = true) (hB : decOK c B LB = true)
    (hsA : D.seedA = String.ofList LA) (hsB : D.seedB = String.ofList LB)
    (h : secK c A B D = true) : (opsP p d).secCheck D = true := by
  subst hp hd
  unfold secK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc] at h
  obtain ⟨hprog, houts, htReg, htests, hrun⟩ := h
  rw [Snd.runC_eq] at hrun
  obtain ⟨h2, hlt⟩ := Snd.progOK_spec hprog
  have hL := SndP.lcorr_regs hc hA hB hsA hsB hprog
  have hlen := Snd.runL_initR_length c D.prog A B D.nregs
  have hT := hL.2 D.tReg (by rw [hlen]; exact htReg)
  have hxs := SndP.forall₂_map hL D.outs (fun r hr => by rw [hlen]; exact Snd.lt_of_all houts hr)
  have hsec := SndP.secOK_of hc hT hxs (fun k hk => Snd.lt_of_all htests hk) hrun
  unfold Ops.secCheck
  simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc]
  exact ⟨h2, hlt, houts, htReg, hsec⟩

end CFSG.KC.OpsLayK

end
