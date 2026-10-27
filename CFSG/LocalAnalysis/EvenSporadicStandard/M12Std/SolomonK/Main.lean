module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.SolomonK.Assembly
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.SolomonK.P12Facts
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.SolomonK.KDSp6SporHolds

public section

namespace CFSG.EvenSporadicStandard.M12Std.SolomonK

open CFSG.LocalAnalysis.ComponentInitial CFSG.Blueprint CFSG.Blueprint.NativeSporadic
  CFSG.ComponentClassification.CatLeaf

theorem solomonA12InputK_of_certs
    (hO : LieOrderFormulasInput)
    (hcard : ∀ s, Nat.card (Carrier s) = CFSG.AGLEmbedding.sporOrd s)
    (hSch : SchreierFor Catalog) (hOdd : OddLieA12Sylow) (hSpor : SporadicNoE64) :
    SolomonA12InputK :=
  solomonA12InputK_of_inputs hSch p12Facts_of_certs
    (kdSp6_of_inputs hO hcard p12Facts_of_certs hOdd hSpor)

theorem solomonA12InputK_of_oddLie
    (hO : LieOrderFormulasInput)
    (hcard : ∀ s, Nat.card (Carrier s) = CFSG.AGLEmbedding.sporOrd s)
    (hSch : SchreierFor Catalog) (hOdd : OddLieA12Sylow) : SolomonA12InputK :=
  solomonA12InputK_of_certs hO hcard hSch hOdd sporadicNoE64_holds

end CFSG.EvenSporadicStandard.M12Std.SolomonK
