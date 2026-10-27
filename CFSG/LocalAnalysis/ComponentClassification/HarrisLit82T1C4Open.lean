module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1C4Main
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P54Reduce
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P54Odd
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P54B
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P54Sp
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P54SU
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P54DBMain
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P54E7
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58bOWire
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58bOLieB
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58bOLieD
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1RowSporHolds
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1RowLie
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1RowAlt
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1Spin410RZ
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1PU1
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1PU4
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51eHolds

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup Assembly.LowTwoRank

section Certified


theorem harris82Theorem1KProper_of_open (hCI : GSLit.ClassicalInvolutionInput)
    (hID : Harris81Lemma35IdentFact) (h3 : Harris82Theorem1FieldThree)
    (hSol : Solomon74SpinSevenAsUsed) :
    Harris82Theorem1KProper :=
  harris82Theorem1KProper_of_inputs hCI TBLit.griessMultipliersAllModels_holds hID
    RowLie.rowLieOther_holds RowAlt.rowAlt_holds RowSpor.rowSpor_holds
    harris82Lemma410Rest_holds harris82Lemma411U1_holds harris82Lemma411U4_holds
    P51e.harris82Lemma51e_holds
    (P54.harris82Lemma54_of_hatFor
        (P54.hatFor_of_rows
            (P54.rowOdd
                (fun X _ t n p f h => Milestones.cl_lit_griess_schur_multipliers_all_native_models X
                    t n p f h)) P54.rowB P54.rowSp P54.rowSL P54.rowSU
            (P54.rowD_of_parts P54.rowDA P54.rowDB) P54.rowE7))
    (harris82Lemma58b_of_lie_rows
      (fun n => harris82Lemma58bRowLie_POmegaOdd TBLit.griessMultipliersAllModels_holds n)
      (fun n => harris82Lemma58bRowLie_POmegaPlus CatLeafProof.lieOrderFormulasInput n)
      (fun n => harris82Lemma58bRowLie_POmegaMinus CatLeafProof.lieOrderFormulasInput n))
    h3 hSol

end Certified

end CFSG.ComponentClassification.HarrisLit.T1
