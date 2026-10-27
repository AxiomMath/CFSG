module

public import CFSG.LocalAnalysis.StandardType.GGLatRootBridge
public import CFSG.LocalAnalysis.StandardType.GGLatOrth
public import CFSG.LocalAnalysis.StandardType.GGExcKnownGroups
public import CFSG.LieType.Universal.Catalog

public section

namespace CFSG.LieType.AschbacherSeitz

open CFSG.Open CFSG.StandardType

@[expose] def GGExcKUniversalInvolutionsAt (t : StatedLieTag) : Prop :=
  ∀ (n f : ℕ), GGExcFive t → 1 ≤ f → ∀ s : (ggU t n f).K, s ≠ 1 → s * s = 1 →
    ∃ g : (ggU t n f).K, ∃ Z : Set (Fin (ggU t n f).D.rank → ℤ),
      ggASClass t n f Z ∧
      g * s * g⁻¹ ∈ ⨆ β ∈ Z, (ggU t n f).D.rootGroup β

end CFSG.LieType.AschbacherSeitz

end
