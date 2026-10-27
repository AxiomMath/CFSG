module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf3DataP1
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf3Bridge

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf.P3

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr

set_option maxHeartbeats 0 in
theorem perm_filter_P1 : ∀ t ∈ dataP1.permWords,
    (∀ r ∈ dataP1.rels, (evalF (dataP1.gensF (ofWr (⟨0, pc t.1⟩ : Wr 8))) r).p = oneF.p) →
      ∃ g ∈ dataP1.goodPerms, gp g = pc t.1 := by
  decide +kernel

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf.P3
