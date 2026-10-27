module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J3KFacts
public import Certificates.Certificate12621

public section

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open CFSG.RankThree.PartTwo.Sec21

theorem gammaWordFacts_holds : GammaWordFacts :=
  Certificates.certificate12621

theorem ks217J3CoverPreimage_holds :
    KS217J3CoverPreimage :=
  ks217J3CoverPreimage_of gammaWordFacts_holds

theorem ks217J3CoverNoTransvection_holds :
    KS217J3CoverNoTransvection :=
  ks217J3CoverNoTransvection_of gammaWordFacts_holds

theorem ks217J3CoverSylowFix_holds :
    KS217J3CoverSylowFix :=
  ks217J3CoverSylowFix_of gammaWordFacts_holds

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
