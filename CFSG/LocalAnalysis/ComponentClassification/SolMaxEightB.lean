module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxEightA
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxFC8Q
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxFCL

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

theorem signalizerNineFusionCountEightInput_of_steps
    (hA : SignalizerNineEightKernelCentralizerInput) (hD : SignalizerNineEightEvenInput)
    (hE : SignalizerNineEightFusionCaseInput) : SignalizerNineFusionCountEightInput := by
  intro X _ _ _ t J e E D S₀ hW M hMH hMpc hJM hHN hsup θ ρ hρ hNoA9 Q Sc hQK hQ2 hQcard htQ hQS
    hSH hS2 hScard htZ hCQ hd3 s hsS hsQ g hgs hgH hs2 hd4 hsN hρs2 hρs1 h5 hsA hsplit
  have hC := hA X t J e E D S₀ hW M hMH hMpc hJM hHN hsup θ ρ hρ hNoA9 Q Sc hQK hQ2 hQcard htQ hQS
    hSH hS2 hScard htZ hCQ hd3 s hsS hsQ g hgs hgH hs2 hd4 hsN hρs2 hρs1 h5 hsA hsplit
  have hQt : Q = zpowers t := eq_zpowers_of_split_of_center htQ hQS htZ hsplit hC
  exact hE X t J e E D S₀ hW M hMH hMpc hJM hHN hsup θ ρ hρ hNoA9 Q Sc hQK hQ2 hQcard htQ hQS
    hSH hS2 hScard htZ hCQ hd3 s hsS hsQ g hgs hgH hs2 hd4 hsN hρs2 hρs1 h5 hsA hsplit hQt
    (hD X t J e E D S₀ hW M hMH hMpc hJM hHN hsup θ ρ hρ hNoA9 Q Sc hQK hQ2 hQcard htQ hQS
      hSH hS2 hScard htZ hCQ hd3 s hsS hsQ g hgs hgH hs2 hd4 hsN hρs2 hρs1 h5 hsA hsplit hQt)

end CFSG.ComponentClassification.SolMax
