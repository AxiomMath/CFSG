module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactParabolicLeviSubExcRed
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ParrottLeviExcUntw
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ParrottLeviExcTriality
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ParrottLeviExcReeF4
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ParrottLeviExcTwE6

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ParrottLeviExc

open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KPLeviSub

theorem leviSubExcInputs_holds :
    LeviSubExcInputs where
  g2 := leviSubAt_g2
  f4 := leviSubAt_f4
  e6 := leviSubAt_e6
  e7 := leviSubAt_e7
  e8 := leviSubAt_e8
  twistedE6 := leviSubAt_twistedE6
  trialityD4 := leviSubAt_trialityD4
  twistedF4 := leviSubAt_twistedF4

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ParrottLeviExc
