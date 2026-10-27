module

public import Certificates.Certificate320016
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupFacts

public section
namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

theorem mcl_lemma45_check :
    McLLem45.check Certificates.MaxD2Heis.mclFiveDataP McLLem45.wordW McLLem45.tree = true :=
  Certificates.certificate320016

theorem mcl_gfree_certified : ExtraFacts IsMcLType 5 McLShape :=
  mcl_gfree mcl_lemma45_check

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
