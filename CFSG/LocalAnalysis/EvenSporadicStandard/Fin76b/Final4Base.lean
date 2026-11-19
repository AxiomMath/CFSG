
module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Final3Base
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.WreathLift
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.BetaTransfer
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.WFacts
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.PinEJ2
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.WCheck
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.WJ2Check
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.BetaJ2
public import CFSG.Sporadic.SmallOddCore.J2DataInputs
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.RootFacts
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverModelsBridge
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutModel
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.PinEJ3
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.WJ3Check
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.BetaJ3
public import CFSG.Sporadic.SmallOddCore.J3DataInputs
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.BetaA5J2
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.BetaA5J3
public import CFSG.Foundations
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCCases

@[expose] public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic

def Fin76bNotZ2A6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (z t : G) (T₀ E : Subgroup G)
    (Q : Sylow 2 G) (x β : G) (B : Subgroup G), Rest6Config L z t T₀ E Q x β B →
    WFacts L t E → ∀ y ∈ normalizer (E : Set G), y * β = β * y → y * z * y⁻¹ = z * t →
      y * t * y⁻¹ = t →
    ¬ Nonempty (↥(centralizer ({β} : Set G)) ⧸ fusionOddCore ↥(centralizer ({β} : Set G)) ≃*
      Multiplicative (ZMod 2) × alternatingGroup (Fin 6))

end CFSG.EvenSporadicStandard.Fin76b
