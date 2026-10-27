module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.Asc77.AscT7ASectA
public import CFSG.ClassicalInvolution.AschTight.Sec19Targets2
public import CFSG.ClassicalInvolution.Uniform.U5Comp
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Uniform

namespace TwinDisc

structure Q8TwinSection (X : Type) [Group X] [Finite X] (Φ : Set (Subgroup X)) : Prop where
  hyp : HypOmegaGen Φ
  two : ∀ J ∈ Φ, IsPGroup 2 (↥J ⧸ classicalInvolutionOddCore ↥J)
  q8 : ∀ J ∈ Φ, ∀ P : Subgroup X, IsSylow2In P J → Nonempty (↥P ≃* QuaternionGroup 2)
  oddFree : classicalInvolutionOddCore X = ⊥
  aEmpty : ∀ J ∈ Φ, AEmpty Φ J
  gen : omegaGen Φ = ⊤
  trans : ∀ K ∈ Φ, ∀ L ∈ Φ, ∃ g : X, conjSub g K = L
  triple : TwinTriple Φ

end TwinDisc

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
