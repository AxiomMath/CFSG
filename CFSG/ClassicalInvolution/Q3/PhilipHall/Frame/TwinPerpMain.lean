module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpWz
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

section Inputs

@[expose] def WCentralNontrivial {Y : Type} [Group Y] (W : Subgroup Y) : Prop :=
  ∃ w ∈ W, w ≠ 1 ∧ ∀ g ∈ Subgroup.normalizer (W : Set Y), g * w = w * g

end Inputs

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
