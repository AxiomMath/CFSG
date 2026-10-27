module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRest11
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInnGoodE7
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInnGoodE8
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompAlgLinear

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

structure KD264LieRest12 : Prop where
  e6 : LieInnGood fun d => ∃ q, d = .E6 q
  twE6 : LieInnGood fun d => ∃ q, d = .twistedE6 q
  a2 : LieCompAlg isUnitaryIdx
  a3 : LieCompAlg isClassicalBCDIdx
  a4 : LieCompAlg isTrialityIdx
  a5 : LieCompAlg isExcUntwistedIdx
  a6 : LieCompAlg isExcTwistedIdx

section Rest12


theorem kd264LieRest11_of_rest12 (h : KD264LieRest12) : KD264LieRest11 :=
  ⟨h.e6, lieInnGood_E7, lieInnGood_E8, h.twE6, lieCompAlg_linear, h.a2, h.a3, h.a4, h.a5, h.a6⟩

end Rest12

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
