module

public import CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator.Assembly
public import CFSG.HardMathSupport.Seitz.G2Anisotropic.ExceptionsTransport.BridgeOdd

public section

open CFSG.Blueprint.Chevalley CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator

namespace CFSG.HardMathSupport.Seitz.G2Anisotropic.ExceptionsTransport

section Generation


theorem g2SplitPairGenerationCentral_proved : G2SplitPairGenerationCentral :=
  fun _ _ _ hK h3 _ => centralizer_sup_top h3 hK

end Generation

section Family


theorem seitzExcAnisotropicG2ThreePlus_of_normalForm (hA : G2SylowPairNormalForm) :
    SeitzExcAnisotropicG2ThreePlus :=
  seitzExcAnisotropicG2ThreePlus_of_residuals hA g2SplitPairGenerationCentral_proved

end Family

end CFSG.HardMathSupport.Seitz.G2Anisotropic.ExceptionsTransport
