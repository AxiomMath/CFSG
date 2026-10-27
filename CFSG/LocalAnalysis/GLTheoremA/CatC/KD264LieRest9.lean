module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRest8
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieTriInnGoodMain

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

structure KD264LieRest9 : Prop where
  innGood : KD264InnGood
  compIdx : KD264CompIdx
  x1ExcE678 : KD264X1ExcE678

section Rest9


theorem kd264LieRest8_of_rest9 (h : KD264LieRest9) : KD264LieRest8 :=
  ⟨h.innGood, kd264TriInnGood_holds, h.compIdx, h.x1ExcE678⟩

end Rest9

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
