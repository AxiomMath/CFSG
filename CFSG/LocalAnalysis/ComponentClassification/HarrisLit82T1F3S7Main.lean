module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3S7Step12
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3Main

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

section Certified


theorem harris82Theorem1FieldThree_of_s7Inputs (h54 : Harris82Lemma54Three)
    (h412 : Harris82Lemma412Three) (hI : S7Inputs) : Harris82Theorem1FieldThree :=
  harris82Theorem1FieldThree_of_inputs h54 hI.fourGroup hI.l58 h412
    (harris82Theorem1SpinSevenThree_of_inputs hI)

end Certified

end CFSG.ComponentClassification.HarrisLit.T1
