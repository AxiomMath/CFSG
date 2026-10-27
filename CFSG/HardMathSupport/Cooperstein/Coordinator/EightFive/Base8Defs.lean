module

public import CFSG.Quasithin.Background.SmithB42Families

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive

open CFSG.Open CFSG.Quasithin

@[expose] def B42L42Core : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ G L : Subgroup (MulAut V),
      (L = quasithinGenFitting G ∧ CFSG.IsQuasisimple ↥L ∧ XMod.IsIrrSec ↥L (⊥ : Subgroup V) ⊤) →
      B42TypeL42 ↥L → ∀ A : Subgroup (MulAut V), IsFFStarOffender G A →
        B42Case9 G L ∨ B42Case10 G L A

end CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive
