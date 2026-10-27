module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3S7Main
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P54F3Final
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3L412
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1RowLie
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1RowAlt
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1RowSporHolds
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51eOdd
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1PU4Three
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3L57
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S74OHolds

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

section Certified


theorem harris82Theorem1FieldThree_of_open (h4 : Harris82FourGroupThree)
    (h58 : Harris82Lemma58bThree) : Harris82Theorem1FieldThree :=
  harris82Theorem1FieldThree_of_s7Inputs
    (P54.F3.harris82Lemma54Three_of_griessNative fun X _ t n p f h =>
      Milestones.cl_lit_griess_schur_multipliers_all_native_models X t n p f h)
    harris82Lemma412Three_holds
    { known := knownRow_of_rows RowLie.rowLieOther_holds RowAlt.rowAlt_holds RowSpor.rowSpor_holds
      fourGroup := h4
      l58 := h58
      l51e := harris82Lemma51eOdd_holds
      u1 := harris82Lemma411U1Three_holds
      u4 := harris82Lemma411U4Three_holds
      l57 := harris82Lemma57SpinThree_holds
      solomon := S74.solomon74SpinSevenAsUsedThree_holds }

end Certified

end CFSG.ComponentClassification.HarrisLit.T1
