module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TwelveLeDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TwelveLeU42O8U42
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TwelveLeU42O8Omega
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TwelveLeU42O8Levi
public import Certificates.Certificate2012
public import Certificates.Certificate4161
public import Certificates.Certificate10010
public import Certificates.Certificate10011
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Pairs
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthMinusHas
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC.Agreement

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TwelveLe

open CFSG.Open CFSG.AGLEmbedding CFSG.QuasithinUnique Subgroup

theorem kFactTwelveLeSolvThree_holds :
    KFactTwelveLeSolvThree := by
  intro A _ _ Y P hY hO hL hP hne _ hperf T hTP hT
  rcases hL with h | h
  · exact U42O8.UFourTwo.card_le_nine_of_parabolic_of_isLieOver hY hO h hP hne hTP hT
  · exact U42O8.OmegaMinusEight.card_le_nine_of_parabolic h hP hperf hTP hT

theorem kFactTwelveLeE27_holds :
    KFactTwelveLeE27 := by
  intro A _ _ Y P E hY hO hL hP h9 hE hE27 hEY hEP hrk
  rcases hL with h | h
  · exact U42O8.UFourTwo.false_of_E27 hY hO h hP h9 hE hE27 hEY hEP hrk
  · exact U42O8.OmegaMinusEight.false_of_E27 h hP h9 hE hE27 hEY hEP hrk

end CFSG.LocalAnalysis.RankThreeTheoremC.TwelveLe
