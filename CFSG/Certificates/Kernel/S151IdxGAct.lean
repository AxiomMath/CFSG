module

public import CFSG.Certificates.Kernel.S151IdxGSound

public section

namespace CFSG.KC.IdxG

open CFSG.KC.E64F CFSG.QuasithinUnique.Ch1.SporLat

variable {n : Nat}

theorem codeSetAct_eq_codeSetF {Δ : List Nat} (hΔ : codesBelow n Δ = true) {t : Array Nat}
    {f : Nat → Nat} (ht : Good n t f) : codeSetAct n t Δ = codeSetF n f Δ := by
  rw [CFSG.KC.SLDc.codeSetAct_eq]
  have e : Δ.map (CFSG.KC.SLDc.codeAT n t) = Δ.map (codeF n f) := by
    refine List.map_congr_left fun c hc => ?_
    have hp := List.all_eq_true.1 (List.all_eq_true.1 hΔ c hc)
    unfold CFSG.KC.SLDc.codeAT codeF
    congr 2
    refine List.map_congr_left fun p hpm => ?_
    exact (ht.2 p (of_decide_eq_true (hp p hpm))).1
  unfold CFSG.KC.SLDc.codeSetT codeSetF
  rw [e]

end CFSG.KC.IdxG

end
