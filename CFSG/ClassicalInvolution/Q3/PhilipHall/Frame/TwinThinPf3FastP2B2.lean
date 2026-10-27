module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf3DataP2
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf3Bridge

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf.P3

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr

set_option maxHeartbeats 0 in
theorem filter_ok_P2 : ∀ g ∈ dataP2.goodPerms, ∀ l ∈ masksN,
    (∀ r ∈ dataP2.rels, eqPF (evalF (dataP2.gensF ⟨l, (ofWr (⟨0, gp g⟩ : Wr 8)).p, (ofWr (⟨0, gp g⟩ : Wr 8)).q⟩) r)
      oneF) →
      ∃ e ∈ dataP2.candsF, eqPF e.1 ⟨l, (ofWr (⟨0, gp g⟩ : Wr 8)).p, (ofWr (⟨0, gp g⟩ : Wr 8)).q⟩ := by
  decide +kernel

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf.P3
