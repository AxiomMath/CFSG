module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263SDLinFam
public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonSubcomp

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T263.SD.Lin

section Certs


theorem t263DescSeed_linHi_holds : T263DescSeed t263GLinHi :=
  t263DescSeed_of_model I142M.Three.chevCompTypes_holds CanonSubcomp.subcompField_holds
    (fun p hp Y _ _ => lBalanceAt_holds Y p hp) (sdFamModel_linHi Y10GInnLin.linLabelDict_holds)

end Certs

end CFSG.LocalAnalysis.GLTheoremA.T263.SD.Lin

end
