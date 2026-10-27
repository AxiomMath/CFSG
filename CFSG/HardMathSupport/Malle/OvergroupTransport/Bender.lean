module

public import CFSG.HardMathSupport.Malle.OvergroupTransport.Transport
public import CFSG.Open.FusionDefs
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113OverBender

public section

namespace CFSG.HardMathSupport.Malle.OvergroupTransport

open CFSG.Open

theorem normalizerMaximal_of_fusionIsBenderGroup {Y : Type} [Group Y] [Finite Y]
    (hB : fusionIsBenderGroup Y) (U : Sylow 2 Y) : NormalizerMaximal (U : Subgroup Y) := by
  have : IsSimpleGroup Y :=
    CFSG.QuasithinUnique.RankOneRecog.isSimpleGroup_of_fusionIsBenderGroup hB
  intro H hH
  by_cases hHt : H = ⊤
  · exact Or.inr hHt
  · refine Or.inl (le_antisymm ?_ hH)
    exact CFSG.QuasithinUnique.Bridge.Over.le_normalizer_of_bender hB U
      (Subgroup.le_normalizer.trans hH) hHt

end CFSG.HardMathSupport.Malle.OvergroupTransport
