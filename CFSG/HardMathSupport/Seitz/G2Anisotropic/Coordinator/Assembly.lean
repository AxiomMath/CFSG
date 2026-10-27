module

public import CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator.Residuals
public import CFSG.HardMathSupport.Seitz.G2Anisotropic.ExceptionsTransport.CatG2BasicProved

public section

open CFSG.HardMathSupport.Seitz.G2Anisotropic.ExceptionsTransport

namespace CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator


theorem seitzExcAnisotropicG2ThreePlus_of_residuals (hA : G2SylowPairNormalForm)
    (hB : G2SplitPairGenerationCentral) : SeitzExcAnisotropicG2ThreePlus :=
  seitzExcAnisotropicG2ThreePlus_of_sylow g2ThreeCatBasic
    (g2ThreeCentralizerPairsSylow_of_native
      (fun q hv K _ _ hK => CFSG.TauCetiBridge.Even.chevalleyBridgesAll.g2 q hv K hK)
      (fun _ _ _ => CFSG.LieType.Chevalley.center_adjointGroup_eq_bot)
      (g2NativeCentralizerPairsSylow_of_residuals hA hB))

end CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator
