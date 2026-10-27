module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.SectionRank.QTK

open CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank

@[expose] def Sp6TwoOrder : Prop :=
  ∀ (H : Type) [Group H], StatedClassicalModel H .PSp 3 2 1 → Nat.card H = 1451520

end CFSG.SectionRank.QTK
