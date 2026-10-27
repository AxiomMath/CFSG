module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.F151Defs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeUniInner
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeUniBlockHoldsMain

public section

namespace CFSG.LocalAnalysis.GLTheoremA.F151

theorem uniDiag_holds :
    DiagHalf (CharTwoOf KD264Lie.isUnitaryIdx) :=
  fun _ _ _ p L J A d b hS hcat hshape hin =>
    T171Sh.innerCompNonShapeW_unitary_charTwo_of_block T171Sh.uniBlockInnDiag_holds
      p L J A d b hS hcat hshape hin

end CFSG.LocalAnalysis.GLTheoremA.F151

end
