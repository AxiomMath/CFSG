module

public import CFSG.HardMathSupport.Seitz.G2Anisotropic.ExceptionsTransport.OddResidual
public import CFSG.HardMathSupport.Seitz.G2Anisotropic.UnitaryEmbedding.PairNormalForm

public section

open CFSG.Blueprint.Chevalley CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator

namespace CFSG.HardMathSupport.Seitz.G2Anisotropic.ExceptionsTransport


theorem seitzExcAnisotropicG2ThreePlus_proved : SeitzExcAnisotropicG2ThreePlus :=
  seitzExcAnisotropicG2ThreePlus_of_normalForm
    CFSG.HardMathSupport.Seitz.G2Anisotropic.UnitaryEmbedding.g2SylowPairNormalForm_of_instances

end CFSG.HardMathSupport.Seitz.G2Anisotropic.ExceptionsTransport
