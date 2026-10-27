module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Export

public section

namespace CFSG.Assembly

open CFSG.HardMathSupport.Solomon.Coordinator.LieComp

theorem e6Four_cover_quot {H L : Type} [Group H] [Group L] (φ : H →* L)
    (hφ : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center H) (hH : commutator H = ⊤) :
    Subgroup.comap φ (Subgroup.center L) = Subgroup.center H ∧
      Nonempty (H ⧸ Subgroup.center H ≃* L ⧸ Subgroup.center L) :=
  ⟨comap_center_of_surjective hH φ hφ hker, nonempty_centralQuotient_mulEquiv hH φ hφ hker⟩

end CFSG.Assembly

end
