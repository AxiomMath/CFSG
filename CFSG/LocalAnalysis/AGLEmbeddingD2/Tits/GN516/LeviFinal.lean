module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.LeviNode
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinParFamily

public section

namespace CFSG.AGLEmbeddingD2.Tits.GN516

open CFSG.Open CFSG.QuasithinUnique CFSG.AGLEmbeddingD2.GN
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
  CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar

@[expose] def ResidualLeviCase : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L S₀ P : Subgroup Y), Open.IsQuasisimple ↥L →
    MinParResidual (↥L ⧸ Subgroup.center ↥L) → IsSylowTwoOf S₀ L → IsMinOverBorel L S₀ P →
      LeviAlt ↥(pElementSubgroup 2 P)

theorem kFactChevMinParabolicLevi_of_families
    (hfam : ∀ (Y : Type) [Group Y] [Finite Y], IsChevTwo Y → HasBQLevi Y ∨ MinParResidual Y)
    (hres : ResidualLeviCase) : KFactChevMinParabolicLevi := by
  intro Y _ _ L S₀ P hL hch hS hP
  rcases hfam _ hch with hbq | hr
  · exact leviAlt_of_hasBQLevi hS hP hbq
  · exact hres Y L S₀ P hL hr hS hP

end CFSG.AGLEmbeddingD2.Tits.GN516
