module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossMain
import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossExcG2
import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossExcF4
import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossExcD4

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

section G2

theorem crossSylowAbelianG2_holds : CrossSylowAbelianG2 := fun _ hv => crossSylowAbelianAt_G2 hv

theorem crossSylowAbelianReeG2_holds : CrossSylowAbelianReeG2 := fun _ hv =>
  crossSylowAbelianAt_reeG2 hv

end G2

section F4

theorem crossSylowAbelianF4_holds : CrossSylowAbelianF4 := fun _ hv => crossSylowAbelianAt_F4 hv

theorem crossSylowAbelianReeF4_holds : CrossSylowAbelianReeF4 := fun _ hv =>
  crossSylowAbelianAt_reeF4 hv

end F4

section D4

theorem crossSylowAbelianTrialityD4_holds : CrossSylowAbelianTrialityD4 := fun _ hv =>
  crossSylowAbelianAt_trialityD4 hv

end D4

end CFSG.LocalAnalysis.RankFourTheoremC
