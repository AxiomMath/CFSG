module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRest9
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX1ExcE678

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

structure KD264LieRest10 : Prop where
  innGood : KD264InnGood
  compIdx : KD264CompIdx

section Rest10


theorem kd264LieRest9_of_rest10 (h : KD264LieRest10) : KD264LieRest9 :=
  ⟨h.innGood, h.compIdx, X1Exc.kd264X1ExcE678_holds⟩

end Rest10

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
