module

public import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.Defs
public import CFSG.HardMathSupport.Lang.D4Three.NormalForm

public section

namespace CFSG.HardMathSupport.Dickson.DefCharOuter.Export

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.LocalAnalysis.GLTheoremA
  CFSG.Yardstones.Md0ec50421ce4
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Lang.D4Three

@[expose] def D4ThreeGraphCent :
    Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 3] (g : adjointGroup Tag.D4 K)
    (a : Fin Tag.D4.rank → Kˣ) (ε : ℕ), 0 < ε → ε < 3 →
      ∀ α : MulAut (adjointGroup Tag.D4 K),
        α = MulAut.conj g * (exactNormalAut Tag.D4 K a (RingEquiv.refl K) 0 * d4Graph K ε) →
        α ^ 3 = 1 → OuterCentData 3 α

end CFSG.HardMathSupport.Dickson.DefCharOuter.Export
