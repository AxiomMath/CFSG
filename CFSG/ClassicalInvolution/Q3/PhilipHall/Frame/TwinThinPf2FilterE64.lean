module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf2DecE64

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr

theorem perm_filter : ∀ t ∈ permWords, (∀ r ∈ relsW, evalW [aW.perm, bW.perm, pc t.1] r = 1) →
    ∃ e ∈ s32, e.1.perm = pc t.1 := by decide +kernel

theorem filter_ok : ∀ t ∈ permWords, (∃ e ∈ s32, e.1.perm = pc t.1) →
    ∀ v : Fin 7 → ZMod 2, ∑ i, v i = 0 →
    (∀ r ∈ relsW, eqπ (evalW [aW, bW, (⟨v, pc t.1⟩ : Wr 7)] r) 1) →
      ∃ e ∈ s32, (⟨v, pc t.1⟩ : Wr 7) = e.1 := by decide +kernel

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf
