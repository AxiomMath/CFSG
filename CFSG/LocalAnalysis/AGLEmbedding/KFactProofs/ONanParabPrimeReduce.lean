module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeCatalog
public import CFSG.LocalAnalysis.ComponentClassification.GoldschmidtTDGriess
public import CFSG.LocalAnalysis.AGLEmbedding.ZZPrimeDefs

public section

namespace CFSG.AGLEmbedding

open CFSG.AGLEmbedding.ParabPrime

 in
theorem kFactParabolicPrime_of_inputs (I : ParabInputs) : KFactParabolicPrime := by
  intro Y _ _ hY hcl T J hT hNJ hJ p hp hp5 hperf
  obtain ⟨q, hcore, hZ⟩ := parabData_of_isClassicalTwoOrG2 I
    CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds hY hcl
  exact parabPrime_of_parabCore (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) hY.1
    hcore hZ hT hNJ hJ hp hp5 hperf

end CFSG.AGLEmbedding
