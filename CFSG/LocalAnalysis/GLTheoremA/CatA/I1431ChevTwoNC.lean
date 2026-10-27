module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ChevTwoExc
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ChevTwoF4
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ChevTwoTwE6
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ChevTwoE
public import CFSG.RankThree.PartTwo.Census.Exceptional.LocalRankThreeTwo

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I1431C2

open CFSG.RankThree.PartTwo.Census.Exceptional

section E


theorem u42FieldTwoAt_E : U42FieldTwoAt fun d => ∃ q, d = .E6 q ∨ d = .E7 q ∨ d = .E8 q :=
  u42FieldTwoAt_E_of_rank (fun q hv hq => four_le_localRank_three_E6_two q hv hq)
    (fun q hv hq => four_le_localRank_three_E7_two q hv hq)
    (fun q hv hq => four_le_localRank_three_E8_two q hv hq)

end E

section NC


theorem u42FieldTwoAt_nonClassical : U42FieldTwoAt U42NonClassical :=
  u42FieldTwoAt_nonClassical_of u42FieldTwoAt_F4 u42FieldTwoAt_twistedE6 u42FieldTwoAt_E

end NC

end CFSG.LocalAnalysis.GLTheoremA.I1431C2

end
