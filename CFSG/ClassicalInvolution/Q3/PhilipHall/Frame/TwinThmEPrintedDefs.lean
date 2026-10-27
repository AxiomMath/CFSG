module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.Asc77.HypOmegaDefs
public import CFSG.ClassicalInvolution.AschTight.S19COrd
public import CFSG.ClassicalInvolution.Q3.TL4D4NCOne
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3

namespace TwinDisc

section Printed

variable {G : Type} [Group G]

@[expose] def CentralizersPrinted (Ω : Set (Subgroup G)) (K W H : Subgroup G) : Prop :=
  ∀ J ∈ KPerp Ω K, ∀ a ∈ K ⊔ J, a ∈ W → a ≠ 1 → a * a = 1 → Subgroup.centralizer ({a} : Set G) ≤ H

end Printed

end TwinDisc

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
