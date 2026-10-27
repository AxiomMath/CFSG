module

public import CFSG.HardMathSupport.Curtis.Coordinator.SeitzTower.Abelian
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFExclusionsTwo

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator.SeitzTower

theorem p1OffCharAlmostSimpleNonNormalAt_suzuki {m : ℕ}
    (hv : (TauCeti.LieTypeIndex.suzuki m).Valid) :
    CFSG.AGLEmbedding.P1OffCharAlmostSimpleNonNormalAt ⟨.suzuki m, hv⟩ := by
  apply p1OffCharAlmostSimpleNonNormalAt_of_outerComm
  intro γ α
  have hS := CFSG.HardMathSupport.Cooperstein.Coordinator.suzukiModel_of_lie hv (MulEquiv.refl _)
  exact CFSG.RankThree.PartTwo.KFacts.KP7.commutatorElement_mem_inner hS γ α

end CFSG.HardMathSupport.Curtis.Coordinator.SeitzTower
