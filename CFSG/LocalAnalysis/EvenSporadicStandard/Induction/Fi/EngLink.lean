module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.Prelim

public section

namespace CFSG.EvenSporadicStandard.Induction.Fi

open CFSG.EvenSporadicStandard.Solomon78

theorem fiLink5bSection : Link5bSection := by
  intro H _ _ N hN hidx hkp P Q hQq hQne hPq hPne T s hQc hsT hPc hincl h5b
  obtain ⟨Y, _, _, N', P', a, b, c, d, e, f, g, h, i, -⟩ :=
    Hyp.link5b_section hN hidx hkp hQq hQne hPq hPne hQc hsT hPc hincl h5b
  exact ⟨Y, inferInstance, inferInstance, N', P', a, b, c, d, e, f, g, h, i⟩

end CFSG.EvenSporadicStandard.Induction.Fi
