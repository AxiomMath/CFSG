module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.P10Ab
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P10Y

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.Tits.N

section Step10


theorem step10_holds : Step10 := by
  intro G _ _ d z₀ h49 hd hz hinv h05 _h06 _h07 h08 h09
  have hsq : z₀ * z₀ = 1 := hinv z₀ hz
  have ht9 : d.t ∉ sylT d ⊓ Subgroup.centralizer ({z₀} : Set G) := h09.2.2.2.2.2.2.2.2.1
  obtain ⟨hsyl, hD, hA, hcard, hVN, hrel⟩ := node10_part_B h49 hd hz h09
  exact ⟨node10_part_C h49 hd hz ht9, node10_V_elemAb h49 hd hz hsq h05 h08 h09 hcard,
    hd.s56_card_V h49 hz, hsyl, hD, hA, hcard, hVN, hrel⟩

end Step10

end CFSG.LocalAnalysis.EvenBN.Tits.N
