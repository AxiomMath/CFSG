module

public import CFSG.LocalAnalysis.OddStandard.Seitz77CaseAClose9
public import CFSG.LocalAnalysis.OddStandard.Seitz77CaseAFromMod
public import CFSG.LocalAnalysis.OddStandard.Seitz77CaseAFromSylow
public import CFSG.LocalAnalysis.OddStandard.Seitz77MainDefs

public section

namespace CFSG.OddStandard.Seitz77

theorem seitz77CaseAFalse :
    Seitz77CaseAFalse := by
  intro G _ _ A V₁ V₂ W X O Sy Wt P h d hR hW H _ hOut
  obtain ⟨κ₀, ρ, Hgl, Xgl, I⟩ := exists_modInput_of_setup27 h d hR hW H hOut
  obtain ⟨S₁, S₀, W₀, ι, κ, φ, S⟩ := exists_sylowA_of_module I
  exact S.false h

end CFSG.OddStandard.Seitz77
