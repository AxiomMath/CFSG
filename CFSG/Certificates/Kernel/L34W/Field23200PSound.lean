module

public import Certificates.Data.Kernel.L34W.Field23200P
public import CFSG.Certificates.Kernel.L34W.Field23200Sound
public import CFSG.Certificates.Kernel.L34W.Tab42Sound

public section

namespace CFSG.KC.L34W

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.L34KSnd
open CFSG.PSL3Four.Native
open CFSG.ComponentClassification.GrSLit.L34Facts CFSG.ComponentClassification.GrSLit.L34Facts.Real

theorem fieldP_eq {T G : ℕ → ℕ} {R : ℕ} (hG : GensG G) (hr2 : r₂T = unpack 42 6 R) (hR : Cn R) :
    fieldK T = fieldP T G R := by
  unfold fieldK fieldP
  refine congrArg (CFSG.KC.Mono.allR 0 64) (funext fun k => ?_)
  obtain ⟨ct, et⟩ := tgK_eq hG k
  rw [strictB_eq23200, et, hr2, comp_unpack' ct hR, comp_unpack' hR ct,
    beq_unpack (CFSG.KC.BfsPin.canonK_pcomp ct hR) (CFSG.KC.BfsPin.canonK_pcomp hR ct)]

theorem fieldK_of_fieldP {T G : ℕ → ℕ} {R : ℕ} (hG : GensG G) (hr2 : r₂T = unpack 42 6 R)
    (hR : Cn R) (h : fieldP T G R = true) : fieldK T = true := by
  rw [fieldP_eq hG hr2 hR]
  exact h

end CFSG.KC.L34W

end
