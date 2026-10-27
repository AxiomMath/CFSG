module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRest7
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264X1ExcF4Conj
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264X1ExcF4Good

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

structure KD264LieRest8 : Prop where
  innGood : KD264InnGood
  triInnGood : KD264TriInnGood
  compIdx : KD264CompIdx
  x1ExcE678 : KD264X1ExcE678

section Rest8


theorem kd264LieRest7_of_rest8 (h : KD264LieRest8) : KD264LieRest7 :=
  ⟨h.innGood, h.triInnGood, h.compIdx, kd264X1ExcPart_of_f4_e678
      (kd264X1ExcF4_of_conj x1F4FrameConj_holds) h.x1ExcE678⟩

end Rest8

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
