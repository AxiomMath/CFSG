module

public import CFSG.LocalAnalysis.RankThreeUC.SourceSetting.AschbacherCommon

public section

namespace CFSG.LocalAnalysis.RankThreeUC

namespace Section6

open CFSG.LocalAnalysis.RankThreeUC

variable {G : Type} [Group G] [Finite G]

structure Context (G : Type) [Group G] [Finite G] (M T : Subgroup G) : Prop where
  uc : SourceSetting.InUC G
  mSigma : SourceSetting.IsInMSigma G M
  sylow : CFSG.ABGLocalTools.IsSylowOf 2 T M

end Section6

end CFSG.LocalAnalysis.RankThreeUC
