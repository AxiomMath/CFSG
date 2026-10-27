module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113DetMain
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113CentMain
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113OverMain
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B113LieRank2
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113DetProved

public section

namespace CFSG.QuasithinUnique.Bridge

open CFSG.Quasithin

theorem asB113_of_timmesfeld
    (hP4 : AsB15Part4) : AsB113With CFSG.SectionRank.IsKGroupCat :=
  asB113With_of_inputs _
      ⟨hP4, B113Det.asB113DetList_of_dichotomy asB42DichotomyNat_proved,
          asLieAltSylowCentralizerList_of asLieRank2SylowAut, Over.asLieAltOvergroupsList_of
          asLieRank2FStar⟩

end CFSG.QuasithinUnique.Bridge
