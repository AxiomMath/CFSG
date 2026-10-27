module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263SKSympModel

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T263.SK

section Certs


theorem t263DescSeed_symp_holds : T263DescSeed t263GSymp :=
  SD.t263DescSeed_of_model I142M.Three.chevCompTypes_holds CanonSubcomp.subcompField_holds
    (fun p hp Y _ _ => lBalanceAt_holds Y p hp) sdFamModel_symp

end Certs

end CFSG.LocalAnalysis.GLTheoremA.T263.SK

end
