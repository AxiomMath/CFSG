module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263SKUniModel
public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonSubcomp

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T263.SK

section Certs


theorem t263DescSeed_uni_holds : T263DescSeed t263GUni :=
  SD.t263DescSeed_of_model I142M.Three.chevCompTypes_holds CanonSubcomp.subcompField_holds
    (fun p hp Y _ _ => lBalanceAt_holds Y p hp) sdFamModel_uni

end Certs

end CFSG.LocalAnalysis.GLTheoremA.T263.SK

end
