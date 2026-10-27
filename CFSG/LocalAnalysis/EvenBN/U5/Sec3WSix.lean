module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.RankThree.PartOne.U5K.Hyp.Coord

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.U5K.Hyp
open scoped commutatorElement

section Generic

variable {G : Type} [Group G]

theorem isElementaryAbelian_of_le' {X Y : Subgroup G} (hY : CFSG.IsElementaryAbelian 2 Y)
    (hXY : X ≤ Y) : CFSG.IsElementaryAbelian 2 X := CFSG.IsElementaryAbelian.of_le hY hXY

end Generic

end CFSG.LocalAnalysis.EvenBN.U5
