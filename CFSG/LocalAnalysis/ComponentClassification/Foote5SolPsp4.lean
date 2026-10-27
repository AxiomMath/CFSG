module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitTypeRank
public import CFSG.RankThree.PartOne.S9.OddCore.TorsionCommon
public import CFSG.Open.StatedAPI
public import CFSG.LocalAnalysis.QuasithinUnique.Setting
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.Quasithin.Background.Basic
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartOne.S9.OddCore.RecognitionBasic
public import CFSG.RankThree.PartOne.S9.StatementsTwoAction

public section

namespace CFSG.ComponentClassification.Foote5.SolMax

open CFSG Subgroup CFSG.Assembly.LowTwoRank Matrix

variable {K : Type} [Field K]

local notation "𝔾" => GL (Fin 2 ⊕ Fin 2) K

end CFSG.ComponentClassification.Foote5.SolMax
