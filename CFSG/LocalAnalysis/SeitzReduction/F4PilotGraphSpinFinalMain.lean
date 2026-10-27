module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotGraphSpinFinalComm

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.EvenSmallLie
  CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatLeaf (GLS3OddLieAutComponentsInput MonsterInnerInput
  MonsterLocalComponentsInput)

section Reduction

theorem e6GraphRowSpinLeviInput_of_agree (hA : E6GraphRowSpinAgreeInput) :
    E6GraphRowSpinLeviInput :=
  e6GraphRowSpinLeviInput_of_agree_pieceComm hA e6RowPieceCommInput_holds

theorem e6GraphRowSpinNormInput_of_agree (hA : E6GraphRowSpinAgreeInput) :
    E6GraphRowSpinNormInput :=
  e6GraphRowSpinNormInput_of_leviInput (e6GraphRowSpinLeviInput_of_agree hA)

end Reduction

end CFSG.SeitzReduction.F4Pilot
