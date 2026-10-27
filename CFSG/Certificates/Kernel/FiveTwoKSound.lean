module

public import Certificates.Data.Kernel.FiveTwoK
public import CFSG.Certificates.Kernel.OpsMcertNSound
public import CFSG.Certificates.Kernel.OpsLayKSnd
import CFSG.Certificates.Kernel.OpsKSound

public section

namespace CFSG.KC.FiveTwoK

open CFSG.SectionRank.Native CFSG.RankThree.Native CFSG.RankThree.PartTwo.Census CFSG.KC.OpsK
  CFSG.KC.OpsMN CFSG.KC.OpsHom CFSG.KC.LQT CFSG.KC.OpsLayK

section Hom

variable {M V₀ V : Type} [Inhabited M] {O₀ : Ops M V₀} {O : Ops Nat V} (H : Hom O₀ O)

theorem movesOK_U (tests : List Nat) {x : Nat} (hx : H.P x) :
    NC2Data.movesOK O₀ tests (H.U x) = movesN O tests x := by
  unfold NC2Data.movesOK movesN
  congr 1
  funext k
  obtain ⟨eu, qu⟩ := H.unit k
  obtain ⟨ev, qv⟩ := H.vmul qu hx
  rw [eu, ev, H.vne qv qu]

theorem check_of_fiveN {A B : Nat} {D : FiveTwoData} (eA : O₀.decode D.base.seedA = H.U A)
    (eB : O₀.decode D.base.seedB = H.U B) (hA : H.P A) (hB : H.P B)
    (h : fiveN O A B D = true) : FiveTwoData.check O₀ D = true := by
  unfold fiveN at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hp, hw⟩, hr⟩ := h
  obtain ⟨Rl, hk, hlen, hR⟩ := regs_of_N H eA eB hA hB hp hr
  obtain ⟨eW, pW⟩ := hR.2 D.w (by rw [hlen]; exact hw)
  unfold orderN at hk
  simp only [Bool.and_eq_true] at hk
  obtain ⟨⟨h10, h5⟩, h2⟩ := hk
  rw [powN_eq O 11 _ 10 (by norm_num)] at h10
  rw [powN_eq O 6 _ 5 (by norm_num)] at h5
  rw [powN_eq O 3 _ 2 (by norm_num)] at h2
  have eR : O₀.run D.base.prog (O₀.initRegs (O₀.decode D.base.seedA) (O₀.decode D.base.seedB)
      D.base.nregs) = O₀.regsOf D.base.seedA D.base.seedB D.base.nregs D.base.prog := rfl
  obtain ⟨e10, p10⟩ := H.pow_U 10 pW
  obtain ⟨e5, p5⟩ := H.pow_U 5 pW
  obtain ⟨e2, p2⟩ := H.pow_U 2 pW
  unfold FiveTwoData.check
  simp only [eR, eW, Bool.and_eq_true, decide_eq_true_eq]
  rw [e10, e5, e2, H.one.1, H.eq p10 H.one.2, movesOK_U H _ p5, movesOK_U H _ p2]
  exact ⟨⟨⟨⟨hp, hw⟩, h10⟩, h5⟩, h2⟩

end Hom

section Lay

theorem movesOK_of_L {c : Lay} (hc : c.ok = true) (hp : c.p = 3) {X : Array CFSG.F3.Native.V}
    {x : Nat} (hX : Snd.LRel c X x) {tests : List Nat} (h : movesL c tests x = true) :
    NC2Data.movesOK (ops3 c.d) tests X = true := by
  unfold movesL at h
  unfold NC2Data.movesOK
  refine Snd.any_mono (fun k _ hk => ?_) h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hk
  obtain ⟨hkd, hne⟩ := hk
  exact Snd.vne_of_vrel hc hp (Snd.vrel_vmul hc hp (Snd.vrel_unit hc hp hkd) hX)
    (Snd.vrel_unit hc hp hkd) (Snd.ne_of_not_beq hne)

theorem check_of_fiveL {c : Lay} {d A B : Nat} {LA LB : List Char} {D : FiveTwoData}
    (hc : c.ok = true) (hp : c.p = 3) (hd : c.d = d)
    (hA : decOK c A LA = true) (hB : decOK c B LB = true)
    (hsA : D.base.seedA = String.ofList LA) (hsB : D.base.seedB = String.ofList LB)
    (h : fiveL c A B D = true) : FiveTwoData.check (ops3 d) D = true := by
  subst hd
  unfold fiveL at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hprog, hw⟩, hrun⟩ := h
  rw [Snd.runC_eq] at hrun
  obtain ⟨-, hlt⟩ := Snd.progOK_spec hprog
  have hL := Snd.lcorr_regs hc hp hA hB hsA hsB hprog
  have hlen := Snd.runL_initR_length c D.base.prog A B D.base.nregs
  have hW := hL.2 D.w (by rw [hlen]; exact hw)
  unfold orderL at hrun
  simp only [Bool.and_eq_true] at hrun
  obtain ⟨⟨h10, h5⟩, h2⟩ := hrun
  unfold FiveTwoData.check
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨⟨hlt, hw⟩, Snd.eq_pow_one hc hp hW (by norm_num) h10⟩,
    movesOK_of_L hc hp (Snd.rel_pow hc hp hW (by norm_num)) h5⟩,
    movesOK_of_L hc hp (Snd.rel_pow hc hp hW (by norm_num)) h2⟩

end Lay

end CFSG.KC.FiveTwoK

end
