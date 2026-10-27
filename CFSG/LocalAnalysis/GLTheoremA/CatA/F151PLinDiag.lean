module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.F151Defs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeLinStatedInner

public section

namespace CFSG.LocalAnalysis.GLTheoremA.F151

theorem linDiag_holds :
    DiagHalf (CharTwoOf KD264Lie.isLinearIdx) :=
  fun _ _ _ p L J A d b hS hcat hshape hin =>
    T171Sh.innerCompNonShapeW_linear_charTwo p L J A d b hS hcat hshape hin

end CFSG.LocalAnalysis.GLTheoremA.F151

end
