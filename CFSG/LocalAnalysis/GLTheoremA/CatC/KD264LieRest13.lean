module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRest12
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInnGoodE6

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

structure KD264LieRest13 : Prop where
  twE6 : LieInnGood fun d => ∃ q, d = .twistedE6 q
  a2 : LieCompAlg isUnitaryIdx
  a3 : LieCompAlg isClassicalBCDIdx
  a4 : LieCompAlg isTrialityIdx
  a5 : LieCompAlg isExcUntwistedIdx
  a6 : LieCompAlg isExcTwistedIdx

section Rest13


theorem kd264LieRest12_of_rest13 (h : KD264LieRest13) : KD264LieRest12 :=
  ⟨lieInnGood_E6, h.twE6, h.a2, h.a3, h.a4, h.a5, h.a6⟩

end Rest13

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
