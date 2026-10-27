module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltCenter
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.H13.L32NSp4Over
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup
open CFSG.Open

@[expose] def InvolutionCentralizerSolvable : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2]
    {b : CFSG.Open.StatedProj (CFSG.Open.StatedSL 3 K)}
    (_ : orderOf b = 2),
    Group.IsSolvable ↥(Subgroup.centralizer ({b} : Set
      (CFSG.Open.StatedProj (CFSG.Open.StatedSL 3 K))))

end CFSG.ComponentClassification.GrSLit.L34Sec5S
