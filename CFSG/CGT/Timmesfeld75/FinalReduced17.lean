module

public import CFSG.CGT.Timmesfeld75.FinalReduced14
public import CFSG.CGT.Timmesfeld75.Sec63Close
public import CFSG.CGT.Timmesfeld75.Sec3TenExc
public import CFSG.CGT.Timmesfeld75.Sec57Close
public import CFSG.CGT.Timmesfeld75.Sec63Final
public import Certificates.Certificate13
public import Certificates.Certificate14
public import Certificates.Certificate15
public import Certificates.Certificate16
public import Certificates.Certificate17
public import Certificates.Certificate18
public import Certificates.Certificate19
public import Certificates.Certificate20
public import Certificates.Certificate21
public import Certificates.Certificate22
public import Certificates.Certificate23
public import Certificates.Certificate24
public import Certificates.Certificate25
public import Certificates.Certificate26
public import Certificates.Certificate27
public import Certificates.Certificate28
public import Certificates.Certificate29
public import Certificates.Certificate30
public import Certificates.Certificate31
public import Certificates.Certificate32
public import Certificates.Certificate33
public import Certificates.Certificate34
public import Certificates.Certificate35
public import Certificates.Certificate36
public import Certificates.Certificate37
public import Certificates.Certificate38
public import Certificates.Certificate39
public import Certificates.Certificate40
public import Certificates.Certificate41
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
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.AschbacherCanonicalRemaining
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ExceptionalEightPlaneCentralizer
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryRootAutomorphism
public import CFSG.Permutation.BurnsideSchur
public import CFSG.Timmesfeld.Moufang.Three
public import CFSG.Timmesfeld.RankOne
public import CFSG.Timmesfeld.Special.TwoCore

public section

namespace CFSG.CGT.Timmesfeld75

theorem sec4NoA_of_inputs
    (L : RemainingLiteratureInputs) (hSz : Section3SzInput)
    (h26 : Lemma26Input) (hI : Sec4CaseIInputs2) (hE : Sec4CaseIIIEight) : Sec4NoA := by
  have h214 := lemma214_of_remaining L
  have hIII : Sec4CaseIII := sec4CaseIII_of_inputs h214 involutionClassInput_of_repo hSz
    L.aschbacherTheoremOne benderWCInput_of_repo hE
  have hCI : Sec4CaseI := sec4CaseI_of_inputs h214 involutionClassInput_of_repo
    L.aschbacherTheoremOne benderWCInput_of_repo aschbacherNoPolarInput_of_repo
    (sec4I4TrivialAction_of_inputs aschbacherNoPolarInput_of_repo
      (lemma215_of_literature
        (LiteratureInputs.of_reduced (ReducedLiteratureInputs.of_remaining L)))
      h26 hI.rootGroup)
    hI.outerAction hI.outerAction5 hI.goldschmidt
  exact sec4NoA_of_cases hCI hIII

end CFSG.CGT.Timmesfeld75
