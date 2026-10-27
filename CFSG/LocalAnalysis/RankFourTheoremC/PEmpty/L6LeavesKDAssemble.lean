module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKDQuot
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.S622Defs

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6KD

theorem s622KFactD_of_kfacts (hEven : KFactFieldAutEven) (hOdd : KFactFieldAutOdd) :
    S622KFactD := by
  intro A _ _ p D V M₀ z hp hp5 hK hzp hzD hpD hV hzV hM₀D H1 H2 _H3
  exact s622_quot_core hp hp5 hK hzp hzD hpD hV hzV hM₀D H1 H2 hEven hOdd

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6KD
