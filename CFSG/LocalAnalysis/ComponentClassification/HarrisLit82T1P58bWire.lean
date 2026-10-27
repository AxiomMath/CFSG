module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58bMain
public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieExcPSL2Odd
public import CFSG.LocalAnalysis.ComponentClassification.GoldschmidtTDGriess
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBClMain

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Assembly.LowTwoRank

theorem harris82Lemma58b_of_open_rows
    (hPSL4 : Harris82Lemma58bNoConfig .PSL 4) (hPSU4 : Harris82Lemma58bNoConfig .PSU 4)
    (hPSp4 : Harris82Lemma58bNoConfig .PSp 2) (hB : ∀ n, Harris82Lemma58bRow .POmegaOdd n)
    (hD : ∀ n, Harris82Lemma58bRow .POmegaPlus n)
    (h2D : ∀ n, Harris82Lemma58bRow .POmegaMinus n) :
    Harris82Lemma58b :=
  harris82Lemma58b_of_rows (fun _ hτ => Foote5.OddLieCore.Exc.noPSLTwoOddCentreComponent_of_mem hτ)
    TBLit.griessMultipliersAllModels_holds CFSG.TauCetiBridge.typewiseBridges
    Burgoyne.burgoynePropBClassicalS_holds hPSL4 hPSU4 hPSp4 hB hD h2D

end CFSG.ComponentClassification.HarrisLit.T1
