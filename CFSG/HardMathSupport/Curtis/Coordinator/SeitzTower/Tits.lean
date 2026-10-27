module

public import CFSG.HardMathSupport.Curtis.Coordinator.SeitzTower.Abelian
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFExclusionsTwo

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator.SeitzTower

theorem p1OffCharAlmostSimpleNonNormalAt_tits
    (hv : TauCeti.LieTypeIndex.tits.Valid) :
    CFSG.AGLEmbedding.P1OffCharAlmostSimpleNonNormalAt ⟨.tits, hv⟩ := by
  have hR : CFSG.Blueprint.ReeTitsModel (TauCeti.CFSGIndex.lie ⟨.tits, hv⟩).Group .Tits 2 1 :=
    CFSG.HardMathSupport.Cooperstein.Coordinator.reeTitsModel_tits_of_lie hv (MulEquiv.refl _)
  have h2 : IsPGroup 2 (CFSG.ComponentClassification.OuterAutomorphisms.Outer
      (TauCeti.CFSGIndex.lie ⟨.tits, hv⟩).Group) :=
    (CFSG.Sporadic.Schreier.Tits.AT_Tits_model_Schreier _ 2 1 hR).1
  refine CFSG.AGLEmbedding.p1OffCharAlmostSimpleNonNormalAt_of_towerOrCover fun p _ hp2 _ _ =>
    Or.inl ?_
  exact outTowerAt_of_isPGroup_outer Nat.prime_two (Fact.out : p.Prime) (Ne.symm hp2) h2

end CFSG.HardMathSupport.Curtis.Coordinator.SeitzTower
