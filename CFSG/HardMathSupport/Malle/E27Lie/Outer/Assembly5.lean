module

public import CFSG.HardMathSupport.Malle.E27Lie.Outer.ExcIndexD4
public import CFSG.HardMathSupport.Lang.E27Lie.TrialityThree
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.HardMathSupport.Malle.E27Lie

open TauCeti

section

theorem trialityThreeLower_holds : TrialityThreeLower :=
  fun hf K _ _ hm α hα3 hαin =>
    CFSG.HardMathSupport.Lang.E27Lie.twentySeven_dvd_fixedSubgroup_trialityD4_three_model hf K hm α
      hα3 hαin

end

end CFSG.HardMathSupport.Malle.E27Lie
