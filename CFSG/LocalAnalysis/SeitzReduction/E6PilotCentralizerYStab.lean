module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotCentralizerYLeviBasic
public import CFSG.Quasithin.Background.A3ComponentsBasic

public section

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.Quasithin (perfectCore)

section Defs

variable (K : Type) [Field K]

@[expose] def LeviStabilizerAS : Prop :=
  ∀ m ∈ parabolicLevi .E6 K nodes16,
    m ∈ centralizer ({(e6ASRep K 1 : ModGL .E6 K)} : Set (ModGL .E6 K)) →
      m ∈ yLeviF4 K ⊔ (torusGroup .E6 K ⊓
        centralizer ({(e6ASRep K 1 : ModGL .E6 K)} : Set (ModGL .E6 K)))

end Defs

section U3

variable {K : Type} [Field K] [CharP K 2]

theorem conj_e6RepConj_e6ASRep_one :
    (MulAut.conj (e6RepConj K 1 : ModGL .E6 K)) (e6ASRep K 1 : ModGL .E6 K) =
      (e6Rep K 1 : ModGL .E6 K) :=
  congrArg Subtype.val (e6RepConj_mul_e6ASRep_mul_inv 1)

end U3

end CFSG.SeitzReduction.E6Pilot
