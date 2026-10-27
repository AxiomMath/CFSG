module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263SDOrthFam
public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonSubcomp

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T263.SD.Orth

open CFSG.LocalAnalysis.GLTheoremA

section Certs


theorem t263DescSeed_orth_of_famSel (hF : FamSelOrth) : T263DescSeed t263GOrth :=
  t263DescSeed_of_model I142M.Three.chevCompTypes_holds CanonSubcomp.subcompField_holds
    (fun p hp Y _ _ => lBalanceAt_holds Y p hp) (sdFamModel_orth Y10GFldOrth.orthLabelDict_holds hF)

theorem t263DescSeed_twOrth_of_famSel (hF : FamSelOrth) : T263DescSeed t263GTwOrth :=
  t263DescSeed_of_model I142M.Three.chevCompTypes_holds CanonSubcomp.subcompField_holds
    (fun p hp Y _ _ => lBalanceAt_holds Y p hp) (sdFamModel_twOrth Y10GFldOrth.orthLabelDict_holds hF)

theorem t263DescSeed_orth_holds : T263DescSeed t263GOrth :=
  t263DescSeed_orth_of_famSel famSelOrth_holds

theorem t263DescSeed_twOrth_holds : T263DescSeed t263GTwOrth :=
  t263DescSeed_twOrth_of_famSel famSelOrth_holds

end Certs

end CFSG.LocalAnalysis.GLTheoremA.T263.SD.Orth

end
