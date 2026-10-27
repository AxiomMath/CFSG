module

public import CFSG.Holt.H78.Sec4Holt
import CFSG.Holt.H78.Sec4Prop46D5

public import Certificates.Certificate43
public import Certificates.Certificate82
public import Certificates.Certificate83
public import Certificates.Certificate84
public import Certificates.Certificate85
public import Certificates.Certificate86
public import Certificates.Certificate87
public import Certificates.Certificate88
public import Certificates.Certificate89
public import Certificates.Certificate90
public import Certificates.Certificate91
public import Certificates.Certificate92
public import Certificates.Certificate93
public import Certificates.Certificate94
public import Certificates.Certificate95
public import Certificates.Certificate96
public import Certificates.Certificate97
public import Certificates.Certificate98
public import Certificates.Certificate99
public import Certificates.Certificate100
public import Certificates.Certificate101
public import Certificates.Certificate102
public import Certificates.Certificate103
public import Certificates.Certificate104
public import Certificates.Certificate105
public import Certificates.Certificate106
public import Certificates.Certificate107
public import Certificates.Certificate108
public import Certificates.Certificate109
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate10007
public import Certificates.Certificate10008
public import CFSG.GH74.Uniqueness.Bender.UnitaryAut
public import CFSG.Holt.H78.Sec4SEAutFix
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderInvUnitary
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderUnitary
public import CFSG.StronglyEmbedded.BenderNormalSeries

public section

namespace CFSG.Holt.H78

theorem holtCaseAStepA7Statement : HoltCaseAStepA7Statement :=
  fun _ _ _ _ _ _ _ _ hS _ _ _ hP => hS.caseAStepA7 hP

theorem holtTheorem1 : HoltTheorem1 :=
  holtTheorem1_of_caseAStepA7 holtCaseAStepA7Statement

end CFSG.Holt.H78
