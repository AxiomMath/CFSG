module

public import Certificates.Data.Kernel.Misc.SignedWordK
public import CFSG.Certificates.Kernel.Misc.ArrEnumSound
public import CFSG.Certificates.Kernel.Misc.ArrEnumOps
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.RuFiveInputs

public section

namespace CFSG.KC.SignedWordK

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum CFSG.Monster.B.Co2.Native
open CFSG.EvenSporadicStandard.RuStd.S2 (signedWordA)

theorem signedWordA_unpack {n w : ℕ} (hw : szOK n w = true) {gs : Array (Array ℕ)}
    {G : ℕ → ℕ} {m : ℕ} (hG : ∀ k < m, gs[k]! = unpack n w (G k))
    (hGp : ∀ k < m, permB n w (G k) = true) (wd : List (ℕ × Bool)) (hl : ∀ l ∈ wd, l.1 < m) :
    signedWordA n gs wd = unpack n w (swK n w G wd) ∧ permB n w (swK n w G wd) = true := by
  induction wd with
  | nil => exact ⟨CFSG.KC.BfsPin.idA_eq hw, permB_of_pp (CFSG.KC.BfsPin.PP.id hw)⟩
  | cons l t ih =>
    obtain ⟨e, p⟩ := ih fun x hx => hl x (List.mem_cons_of_mem _ hx)
    obtain ⟨k, b⟩ := l
    have hk : k < m := hl (k, b) List.mem_cons_self
    cases b
    · have hp := permB_pinvS hw (hGp k hk)
      refine ⟨?_, permB_pcomp hw hp p⟩
      simp only [signedWordA, swK, cond_false, Bool.false_eq_true, ↓reduceIte]
      rw [e, hG k hk, inv_unpack hw (hGp k hk), comp_unpack hw hp p]
    · refine ⟨?_, permB_pcomp hw (hGp k hk) p⟩
      simp only [signedWordA, swK, cond_true, ↓reduceIte]
      rw [e, hG k hk, comp_unpack hw (hGp k hk) p]

end CFSG.KC.SignedWordK

end
