module

public import Certificates.Data.Kernel.LocalQT.M24L
public import CFSG.Certificates.Kernel.LocalQTWordSound
import CFSG.Certificates.Kernel.LocalQTLatKSound
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3Invo
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3Cert

public section

namespace CFSG.KC.LQT.M24Snd

open Equiv CFSG.QuasithinUnique.A5.Kc3Cert CFSG.QuasithinUnique.Vol2Native.A312L.PermLat
  CFSG.QuasithinUnique.Unc25K1.Six CFSG.KC.LQT.W

theorem x0_snd {n : ℕ} (hn : n ≤ 32) (gs : List (Perm (Fin n))) (xW : List ℕ)
    (h : CFSG.KC.LQT.M24.x0K n (gs.map codeP) xW = true) :
    (xPow (evalW (gs.map RN.enc) xW) 5 == 1 && evalW (gs.map RN.enc) xW != 1) = true := by
  have hX : CFSG.KC.LQT.M24.x0K n (gs.map codeP) xW =
      (CFSG.KC.Ord.andB (Nat.beq (CFSG.KC.LQT.P.pow n (CFSG.KC.LQT.P.code (evalW gs xW)) 5)
        (CFSG.KC.LQT.P.one n)) (CFSG.KC.Ord.notB (Nat.beq (CFSG.KC.LQT.P.code (evalW gs xW))
        (CFSG.KC.LQT.P.one n)))) := by
    have hev : evalWK n (gs.map codeP) xW = CFSG.KC.LQT.P.code (evalW gs xW) :=
      CFSG.KC.LQT.LK.evalWK_code hn gs xW
    unfold CFSG.KC.LQT.M24.x0K
    rw [hev, CFSG.KC.LQT.P.letB_eq]
  rw [hX, CFSG.KC.LQT.P.andB_iff, CFSG.KC.LQT.P.notB_iff] at h
  obtain ⟨h1, h2⟩ := h
  have h1' : evalW gs xW ^ 5 = 1 := by
    have := CFSG.KC.LQT.P.beq_iff.1 h1
    rw [CFSG.KC.LQT.P.code_pow hn, CFSG.KC.LQT.P.code_one] at this
    exact CFSG.KC.LQT.P.code_inj hn this
  have h2' : evalW gs xW ≠ 1 := by
    intro e
    apply h2
    rw [e, ← CFSG.KC.LQT.P.code_one]
    exact Nat.beq_refl _
  have e1 : evalW (gs.map RN.enc) xW = RN.enc (evalW gs xW) :=
    (enc_evalW (rawIsEnc n) gs xW).symm
  rw [e1]
  have e2 : xPow (RN.enc (evalW gs xW)) 5 = 1 := by
    rw [← enc_pow (rawIsEnc n), h1', RN.enc_one]
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq]
  exact ⟨e2, fun e => h2' ((rawIsEnc n).inj (e.trans RN.enc_one.symm))⟩

end CFSG.KC.LQT.M24Snd

end
