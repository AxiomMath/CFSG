module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterPumpTType
public import CFSG.LocalAnalysis.OddStandard.AltStdBalCMain
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterPumpType

public section

namespace CFSG.EvenSporadicStandard.HSStd.PumpT

open Subgroup CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer CFSG.OddStandard.AltStdBal

theorem solomonIAltCentralizer_proved : SolomonIAltCentralizer := by
  intro G _ _ L h n hn e S
  obtain ⟨-, hev, -⟩ := h.standard
  obtain ⟨S₀, hS₀⟩ := h.cyclicSylow
  have hcyc : IsCyclic ↥S := (MulEquiv.isCyclic (Sylow.equiv S S₀)).mpr hS₀
  rcases card_eq_two_or_four_le hev S with h2 | h4
  · exact h2
  · exact (altStdBalancedBig_holds G L ⟨h.simple, h.nonabelian, h.kProper, h.standard⟩ n hn e S
      hcyc h4 fun z hz => h.oddCore z hz).elim

end CFSG.EvenSporadicStandard.HSStd.PumpT
