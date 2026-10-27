module

public import Certificates.Data.Kernel.OpsLayGKFT
public import CFSG.Certificates.Kernel.OpsLayGKFSound
import CFSG.Certificates.Kernel.OpsLayTSound

public section

namespace CFSG.KC.OpsLayGKF

open CFSG.SectionRank.Native CFSG.GH74.Generic.Fusion CFSG.GH74.KGroups.J3 CFSG.KC.LQT
  CFSG.KC.OpsLayK CFSG.KC.OpsV4

theorem gkfFusKT_eq (c : Lay) (A B : Nat) (D : FusData) : gkfFusKT c A B D = gkfFusK c A B D := by
  unfold gkfFusKT gkfFusK
  rw [runCT_eq, Snd.runC_eq, regs_tree]

theorem gkfFusKP_sound {c : Lay} {p d A B : Nat} {LA LB : List Char} {D : FusData}
    (hc : c.ok = true) (hp : c.p = p) (hd : c.d = d)
    (hA : decOK c A LA = true) (hB : decOK c B LB = true)
    (hsA : D.seedA = String.ofList LA) (hsB : D.seedB = String.ofList LB)
    (h : gkfFusK c A B D = true) : fusCheck (opsP p d) D = true := by
  subst hp hd
  unfold gkfFusK at h
  rw [Snd.runC_eq] at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨hprog, ho⟩, htests⟩, hexp⟩, hrun⟩ := h
  obtain ⟨hn, hlt⟩ := Snd.progOK_spec hprog
  have hL := SndP.lcorr_regs hc hA hB hsA hsB hprog
  have hlen := Snd.runL_initR_length c D.prog A B D.nregs
  refine fusCheck_of_G (Sim.ofLP c hc) hn hlt ho (fun r hr => hL.2 r (by rw [hlen]; exact hr))
    (fun k hk => Snd.lt_of_all htests hk) (fun k hk => ?_) hrun
  have h2 := List.all_eq_true.1 hexp k (List.mem_range.2 hk)
  rw [Bool.and_eq_true] at h2
  exact ⟨(of_decide_eq_true h2.1 : D.n1s.getD k 0 < 65536),
    (of_decide_eq_true h2.2 : D.n2s.getD k 0 < 65536)⟩

end CFSG.KC.OpsLayGKF

end
