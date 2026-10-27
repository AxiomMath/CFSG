module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRest6
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX2E6TNA

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

structure KD264LieRest7 : Prop where
  innGood : KD264InnGood
  triInnGood : KD264TriInnGood
  compIdx : KD264CompIdx
  x1Exc : KD264X1ExcPart

section Rest7Six

theorem kd264LieRest6_of_rest7 (h : KD264LieRest7) : KD264LieRest6 :=
  ⟨h.innGood, h.triInnGood, h.compIdx, h.x1Exc, X2E6.T.x2e6TorusGood9_holds⟩

end Rest7Six

section Rest7

theorem kd264LieInputs_of_rest7 (h : KD264LieRest7) : KD264LieInputs :=
  kd264LieInputs_of_rest6 (kd264LieRest6_of_rest7 h)

end Rest7

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
