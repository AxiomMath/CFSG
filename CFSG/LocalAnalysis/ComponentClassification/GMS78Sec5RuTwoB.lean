module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuTwo
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuGammaS5

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.Quasithin CFSG.ABGLocalTools
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard CFSG.BenderSuzuki.PFAppendixIII
open CFSG.GMS78Ru CFSG.GMS78RuSim CFSG.GMS78RuQ

theorem Sec3.SzR.dempwolff218Hyp (G : Type) [Group G] [Finite G] : Sec3.SzR.Dempwolff218Hyp G :=
  fun hX hXc hZX hZc hZcen hXn hJ hidx htr =>
    RuGamma.dempwolff218 hX hXc hZX hZc hZcen hXn hJ hidx htr

end CFSG.ComponentClassification.GMS78
