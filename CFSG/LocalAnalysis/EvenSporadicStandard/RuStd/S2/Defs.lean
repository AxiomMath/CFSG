module

public import CFSG.LieType.Multipliers.U43Action
public import CFSG.LocalAnalysis.ComponentClassification.GeneralizedFitting
public import CFSG.LocalAnalysis.SectionRank.NativeKGroup

public section

namespace CFSG.EvenSporadicStandard.RuStd.S2

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic

abbrev A5 : Type := alternatingGroup (Fin 5)

abbrev A6 : Type := alternatingGroup (Fin 6)

abbrev M10 : Type := ↥(MulAction.stabilizer ↥NativeSporadic.M11 (0 : Fin 11))

abbrev U43 : Type := CFSG.LieType.Multipliers.U43.X₀

abbrev Q8 : Type := QuaternionGroup 2

noncomputable abbrev fStar (X : Type*) [Group X] : Subgroup X :=
  CFSG.ComponentClassification.GeneralizedFitting.subgroup X

@[expose] def GHLemma53_1 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.SectionRank.IsKGroupCat X → CFSG.oddCore X = ⊥ →
    ∀ t : X, orderOf t = 2 →
    t ∉ center X →
    Nonempty (↥(centralizer ({t} : Set X)) ≃* (Multiplicative (ZMod 2) × M10)) →
    Nonempty (↥(fStar X) ≃* U43) ∨ Nonempty (↥(fStar X) ≃* (A6 × A6))

@[expose] def OutU43TwoGroup : Prop :=
  IsPGroup 2 (CFSG.ComponentClassification.OuterAutomorphisms.Outer U43)

end CFSG.EvenSporadicStandard.RuStd.S2
