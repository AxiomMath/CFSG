module

public import Certificates.Data.Kernel.BfsPin
public import Certificates.Data.Kernel.Misc.PermClos
import CFSG.Certificates.Kernel.LocalQTPermSound
import CFSG.Certificates.Kernel.Spor.Loops
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

namespace CFSG.KC.BfsPin

open CFSG.KC.LQT CFSG.KC.Misc.Clos

theorem distinctK_of_sortAt {N : Nat} {T S : Nat → Nat} (hs : ∀ i < N, sortAt N T S i = true)
    (hm : Nat.beq (CFSG.KLie.CT.orN N fun k => CFSG.KLie.CT.pw2 (S k)) (CFSG.KLie.CT.maskN N) =
      true) : distinctK N T S = true := by
  have h1 : ∀ i < N, S i < N ∧ (i + 1 < N → T (S i) < T (S (i + 1))) := by
    intro i hi
    obtain ⟨ha, hb⟩ := P.andB_iff.1 (hs i hi)
    exact ⟨Nat.blt_eq.mp ha, fun h => Nat.blt_eq.mp (P.impB_iff.1 hb (Nat.blt_eq.mpr h))⟩
  unfold distinctK
  refine (CFSG.KS.bAnd_iff _ _).2 ⟨CFSG.KS.Raw.Orb.allN_iff.2 fun k hk => ?_,
    (CFSG.KS.bAnd_iff _ _).2 ⟨CFSG.KS.Raw.Orb.allN_iff.2 fun k hk => ?_, hm⟩⟩
  · have hk' : k < N - 1 := hk
    exact Nat.blt_eq.mpr ((h1 k (by omega)).2 (by omega))
  · exact Nat.blt_eq.mpr (h1 k hk).1

end CFSG.KC.BfsPin

end
