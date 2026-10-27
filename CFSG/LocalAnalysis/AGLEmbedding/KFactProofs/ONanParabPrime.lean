module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeReduce
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeTwoSL
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeTwoSp
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeTwoSpin
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeTwoSpinMinus
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeTwoSU

public section

namespace CFSG.AGLEmbedding

open CFSG.AGLEmbedding.ParabPrime

 in
theorem kFactParabolicPrime : KFactParabolicPrime :=
  kFactParabolicPrime_of_inputs
    ⟨parabCore_of_model_psu, parabCore_of_model_psl_two, parabCore_of_model_psu_two,
      parabCore_of_model_psp_two, parabCore_of_model_pomegaPlus_two,
      parabCore_of_model_pomegaMinus_two⟩

end CFSG.AGLEmbedding
