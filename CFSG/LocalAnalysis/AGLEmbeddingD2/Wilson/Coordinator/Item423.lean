module

public import CFSG.RankThree.PartTwo.Sec4.Item423Res5ProofUse
public import CFSG.RankThree.PartTwo.Sec4.Item45Closed
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.K423Cover.Main
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.MaximalityAmbient.AlphaU43.Main
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Census423Three.G2Census
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Proving.ThetaCentOfHe
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.ThetaSpor.RuThetaCentOf
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.ThetaCentSeven

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Coordinator

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo


theorem item4_23_of_six
    (h46 : Sec4.Item4_6) (h6 : Sec4.K423Inner46SixLieRest) : Sec4.Item4_23 :=
  Sec4.item4_23_of_res5 Sec4.rank3II_4_5 h46 (K423Cover.k423CoverFrame_of_u43
      MaximalityAmbient.AlphaU43.alphaNine_U43)
    Census423Three.k423Inner46Three_holds (CFSG.AGLEmbeddingD2.Wilson.Coordinator.k423SporThetaCent_of
        (CFSG.AGLEmbeddingD2.Wilson.Proving.thetaCentOf_he)
        (CFSG.AGLEmbeddingD2.Wilson.ThetaSpor.thetaCentOf_ru)) h6 k423ThetaCentSeven
    Sec4.k423Inner46EightRest_holds

end CFSG.AGLEmbeddingD2.Wilson.Coordinator
