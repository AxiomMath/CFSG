module

public import CFSG.LieType.Chevalley.ParabolicRootFactorData

public section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley

theorem parabolicRoots_mono {τ : Tag} {J J' : Set (Fin τ.rank)}
    (h : J ⊆ J') :
    parabolicRoots τ J ⊆ parabolicRoots τ J' := by
  rintro α ⟨hα, hsupp⟩
  exact ⟨hα, fun i hi => hsupp i (fun hiJ => hi (h hiJ))⟩

end CFSG.LieType.Chevalley
