module

public import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.Defs

public section

namespace CFSG.HardMathSupport.Dickson.DefCharOuter.Export

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.LocalAnalysis.GLTheoremA
  CFSG.Yardstones.Md0ec50421ce4

@[expose] def D4ThreeOuterCent : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.D 4 q).Valid),
    Nonempty (S ≃* TauCeti.ValidLieTypeIndex.Group ⟨.D 4 q, hv⟩) → q.p = 3 →
      ∀ β : MulAut S, β ^ 3 = 1 → β ∉ innerAut S → OuterCentData 3 β

end CFSG.HardMathSupport.Dickson.DefCharOuter.Export
