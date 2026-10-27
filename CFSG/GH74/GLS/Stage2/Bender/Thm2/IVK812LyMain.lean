module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67LyOutPerm
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2.IVK812

open Subgroup CFSG CFSG.Blueprint CFSG.GH74.GLS.Stage2.Bender.Thm1

@[expose] def LyThreeAOuter : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], NativeSporadic.IsSporadic Y .Ly →
    ∀ x : Y, orderOf x = 3 → Nat.card ↥(centralizer ({x} : Set Y)) = 2694384000 →
      ∀ A : Subgroup Y, Nat.card ↥A = 2 ^ 8 → A ≤ normalizer (zpowers x : Set Y) →
        ∀ W : Subgroup Y, IsPGroup 3 ↥W → W ≤ normalizer (zpowers x : Set Y) →
          A ≤ normalizer (W : Set Y) → W ≤ zpowers x

end CFSG.GH74.GLS.Stage2.Bender.Thm2.IVK812
