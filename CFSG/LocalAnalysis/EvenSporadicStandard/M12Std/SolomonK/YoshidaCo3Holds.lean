module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.SolomonK.Main
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.SolomonK.OddLie.Assembly
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.SolomonK.YoshidaLocal

public section

namespace CFSG.EvenSporadicStandard.M12Std.SolomonK

open CFSG.LocalAnalysis.ComponentInitial CFSG.Blueprint CFSG.Blueprint.NativeSporadic
  CFSG.ComponentClassification.CatLeaf

theorem solomonA12InputK_of_orders
    (hO : LieOrderFormulasInput)
    (hcard : ∀ s, Nat.card (Carrier s) = CFSG.AGLEmbedding.sporOrd s)
    (hSch : SchreierFor Catalog) : SolomonA12InputK :=
  solomonA12InputK_of_oddLie hO hcard hSch (OddLie.oddLieA12Sylow_of
      (sylowData_elemFactsIn (card_alt_two_part (Or.inl rfl))
          (P12.p12Check_sound Certificates.certificate450015)) hO)

theorem yoshida74Co3K_of_orders
    (hO : LieOrderFormulasInput)
    (hcard : ∀ s, Nat.card (Carrier s) = CFSG.AGLEmbedding.sporOrd s)
    (hSch : SchreierFor Catalog) : Yoshida74Co3K :=
  yoshida74Co3K_of_localK yoshida74LocalK_holds (solomonA12InputK_of_orders hO hcard hSch)

end CFSG.EvenSporadicStandard.M12Std.SolomonK
