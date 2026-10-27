module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1432LieForkDefs
import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.Assembly
import CFSG.LocalAnalysis.GLTheoremA.CatB.H1432LieForkLin
import CFSG.LocalAnalysis.GLTheoremA.CatB.H1432LieForkSp
import CFSG.LocalAnalysis.GLTheoremA.CatB.H1432LieForkOrthA
import CFSG.LocalAnalysis.GLTheoremA.CatB.H1432LieForkD4Fam
import CFSG.LocalAnalysis.GLTheoremA.CatB.H1432LieForkD4
import CFSG.LocalAnalysis.GLTheoremA.CatB.H1432LieForkExcA
import CFSG.LocalAnalysis.GLTheoremA.CatB.H1432LieForkExcB
import CFSG.LocalAnalysis.GLTheoremA.CatB.H1432LieForkTwE6
import CFSG.LocalAnalysis.GLTheoremA.CatB.H1432LieForkRee
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1420

open CFSG.HardMathSupport.Dickson.Sec6 (fam_cover_three)


theorem lieOuterThree_holds : LieOuterThree := by
  intro P _ _ t n f hadm _ hm ψ hψ3 hψ
  have ht : t ≠ .Tits := by
    rintro rfl
    have := hadm.2.2.2.1
    omega
  rcases fam_cover_three hadm ht with
    h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact lieOuterThreeAt_pslTwo P t n f hadm h hm ψ hψ3 hψ
  · exact lieOuterThreeAt_pslGood P t n f hadm h hm ψ hψ3 hψ
  · exact lieOuterThreeAt_psp P t n f hadm h hm ψ hψ3 hψ
  · exact lieOuterThreeAt_psuGood P t n f hadm h hm ψ hψ3 hψ
  · exact lieOuterThreeAt_orthOdd P t n f hadm h hm ψ hψ3 hψ
  · exact lieOuterThreeAt_orthPlus P t n f hadm h hm ψ hψ3 hψ
  · exact lieOuterThreeAt_orthMinus P t n f hadm h hm ψ hψ3 hψ
  · exact lieOuterThreeAt_d4_of_cases d4ThreeOuterCases_holds P t n f hadm h hm ψ hψ3 hψ
  · exact lieOuterThreeAt_triD4 P t n f hadm h hm ψ hψ3 hψ
  · exact lieOuterThreeAt_g2 P t n f hadm h hm ψ hψ3 hψ
  · exact lieOuterThreeAt_f4 P t n f hadm h hm ψ hψ3 hψ
  · exact lieOuterThreeAt_e6 P t n f hadm h hm ψ hψ3 hψ
  · exact lieOuterThreeAt_twE6 P t n f hadm h hm ψ hψ3 hψ
  · exact lieOuterThreeAt_e7 P t n f hadm h hm ψ hψ3 hψ
  · exact lieOuterThreeAt_e8 P t n f hadm h hm ψ hψ3 hψ
  · exact lieOuterThreeAt_reeG2 P t n f hadm h hm ψ hψ3 hψ

end CFSG.LocalAnalysis.GLTheoremA.H1420

end
