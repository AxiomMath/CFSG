module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58bWire
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58bL4
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58bU4
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58bSp4
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58bOSL

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Assembly.LowTwoRank

theorem harris82Lemma58b_of_lie_rows
    (hB : ∀ n, Harris82Lemma58bRowLie .POmegaOdd n)
    (hD : ∀ n, Harris82Lemma58bRowLie .POmegaPlus n)
    (h2D : ∀ n, Harris82Lemma58bRowLie .POmegaMinus n) : Harris82Lemma58b :=
  harris82Lemma58b_of_open_rows noConfig_PSL_four noConfig_PSU_four noConfig_PSp_two
      (fun n => harris82Lemma58bRow_of_sl_of_lie
          (harris82Lemma58bRowSL_POmegaOdd TBLit.griessMultipliersAllModels_holds n) (hB n))
      (fun n => harris82Lemma58bRow_of_sl_of_lie (harris82Lemma58bRowSL_POmegaPlus n) (hD n))
      (fun n => harris82Lemma58bRow_of_sl_of_lie (harris82Lemma58bRowSL_POmegaMinus n) (h2D n))

end CFSG.ComponentClassification.HarrisLit.T1
