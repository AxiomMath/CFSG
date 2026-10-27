module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf3DataP3
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf3Bridge

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf.P3

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr

set_option maxHeartbeats 0 in
theorem perm_filter_P3 : ∀ t ∈ dataP3.permWords,
    (∀ r ∈ dataP3.rels, (evalF (dataP3.gensF (ofWr (⟨0, pc t.1⟩ : Wr 8))) r).p = oneF.p) →
      ∃ g ∈ dataP3.goodPerms, gp g = pc t.1 := by
  decide +kernel

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf.P3
