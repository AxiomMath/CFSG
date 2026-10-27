module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieOuterIdxLinear
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieOuterIdxUnitary
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieOuterIdxClassical
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieOuterIdxTriality
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieOuterIdxExc
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieOuterIdxExcTwisted
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieOutCycAll
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieI5Low
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieI5Aut

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

structure KD264LieRest : Prop where
  innGood : KD264InnGood
  triInnGood : KD264TriInnGood
  compIdx : KD264CompIdx
  i5Field : KD264I5Field
  x1Row : KD264X1Row
  xUnRow : KD264XUnRow
  x2E6Row : KD264X2E6Row
  y1Row : KD264Y1Row
  f8Row : KD264F8Row

section Rest


theorem kd264LieInputs_of_rest (h : KD264LieRest) : KD264LieInputs :=
  ⟨kd264OutCyc_holds, kd264OuterIdx_of_families lieOuterIdx_linear lieOuterIdx_unitary
      lieOuterIdx_classicalBCD lieOuterIdx_triality lieOuterIdx_excUntwisted lieOuterIdx_excTwisted, h.innGood, h.triInnGood, h.compIdx, h.i5Field, kd264I5Low_holds,
    kd264I5Aut_holds, h.x1Row, h.xUnRow, h.x2E6Row, h.y1Row, h.f8Row⟩

end Rest

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
