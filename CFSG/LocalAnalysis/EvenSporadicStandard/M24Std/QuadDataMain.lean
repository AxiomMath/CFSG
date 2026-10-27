module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.QuadDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.QuadDataFix
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.QuadDataGen
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.QuadDataOmega

public section

namespace CFSG.EvenSporadicStandard.M24Std

variable {G : Type} [Group G]

theorem sextetFactsQW_of_type
    {L A : Subgroup G} (h : SextetType L A) : SextetFactsQW L A :=
  ⟨gen45W_of_type h, fix_of_type h, omegaW_of_type h⟩

end CFSG.EvenSporadicStandard.M24Std
