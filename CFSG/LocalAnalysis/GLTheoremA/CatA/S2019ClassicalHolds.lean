module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019OrthD4GraphTypeHolds
import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019ClassicalReduce
import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019LinInner
import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019LinInnerThree
import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019LinOuter
import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019UniInner
import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019UniInnerThree
import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019UniOuter
import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019SympInnerThree
import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019OrthInnerThree

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S2019

section Holds


theorem s2019OrthD4Outer_holds : S2019OrthD4Outer :=
  s2019OrthD4Outer_of_graphType s2019OrthD4GraphType_holds

theorem s2019FactClassical_holds : S2019FactClassical :=
  s2019FactClassical_of_on fun F => by
    cases F with
    | linear =>
      exact s2019FactClassicalOn_linear s2019LinInner_five s2019LinInner_three s2019LinOuter
    | unitary =>
      exact s2019FactClassicalOn_unitary s2019UniInner_five s2019UniInner_three s2019UniOuter
    | symplectic => exact s2019FactClassicalOn_symplectic_proved
    | orthogonal => exact s2019FactClassicalOn_orthogonal_of_D4Outer s2019OrthD4Outer_holds

end Holds

end CFSG.LocalAnalysis.GLTheoremA.S2019
