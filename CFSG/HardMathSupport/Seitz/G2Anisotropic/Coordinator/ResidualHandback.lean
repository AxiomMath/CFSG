module

public import CFSG.HardMathSupport.Seitz.G2Anisotropic.UnitaryEmbedding.G2NativePlus
public import CFSG.HardMathSupport.Seitz.ExceptionsTransport.G2NativeSplit
public import CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator.G2NativeCyclic
public import CFSG.LieType.SeitzGeneration.ExcAnisotropicAssembly

public section

open CFSG.LieType.SeitzGeneration

namespace CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator


theorem seitzExcAnisotropicG2NineFive_proved : SeitzExcAnisotropicG2NineFive :=
  SeitzExcAnisotropicFor.toAt (seitzExcAnisotropicG2_of_parts
      CFSG.HardMathSupport.Seitz.ExceptionsTransport.g2NativePlaneGenSplit_proved
      UnitaryEmbedding.g2NativePlaneGenPlus_proved g2NativePlaneGenCyclic) _

theorem seitzExcAnisotropicG2ThreeMinus_proved : SeitzExcAnisotropicG2ThreeMinus :=
  SeitzExcAnisotropicFor.toAt (seitzExcAnisotropicG2_of_parts
      CFSG.HardMathSupport.Seitz.ExceptionsTransport.g2NativePlaneGenSplit_proved
      UnitaryEmbedding.g2NativePlaneGenPlus_proved g2NativePlaneGenCyclic) _

end CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator
