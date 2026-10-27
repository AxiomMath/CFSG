module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRest13
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInnGoodTwE6
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompAlgUnitary
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompAlgTriality
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompAlgExcTw

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

section Rest14


theorem kd264LieRest13_of_rest14 (ha3 : LieCompAlg isClassicalBCDIdx) (hE6O : E6D4OuterNotEight)
    (hE6C : E6EightCentralizerConn) : KD264LieRest13 :=
  ⟨lieInnGood_twistedE6, lieCompAlg_unitary, ha3, lieCompAlg_triality,
    lieCompAlg_excUntwisted_of_E6res_kd264alg hE6O hE6C,
    lieCompAlg_excTwisted_of_E6res_kd264alg hE6O hE6C⟩

end Rest14

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
