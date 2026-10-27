module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SStdSplit
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SONanCoreHolds

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

theorem l34SuzONanFieldPumpUpExclusion_of_five_residuals
    (hCI : GSLit.ClassicalInvolutionInput) (h13 : Sol76T13.SolomonThm13Simple)
    (hSSuz : L34SuzStandardExclusion) (hSON : L34ONanStandardExclusion)
    (hSField : L34FieldStandardExclusion) (hCSuz : L34SuzCoreStepMirror)
    (hCField : L34FieldCoreStepMirror) :
    L34SuzONanFieldPumpUpExclusion :=
  l34SuzONanFieldPumpUpExclusion_of_residuals hCI h13 hSSuz hSON hSField hCSuz
    (l34ONanCoreStepMirror_holds hCI h13) hCField

end CFSG.ComponentClassification.GrSLit.L34Sec5S
