module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CSideOdd
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.EvenSporadicStandard.M24Std

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank

theorem CData.isKGroupCat_egQD {G : Type} [Group G] {A C : Subgroup G} {z : G}
    (hKS : KLocalSections G) (hC : CData A z C) : CFSG.SectionRank.IsKGroupCat (egQD C) := by
  refine hKS C (fun h => ?_) hC.comm
  have := hC.card
  rw [h, Subgroup.card_bot] at this
  omega

namespace CSide

variable {G : Type} [Group G] [Finite G] {L A C : Subgroup G} {z : G}

theorem cLayerDisjIso (hHS : HarrisSolomonZ2S6IsoK) (hK : CFSG.SectionRank.IsKGroupCat (egQD C))
    (h : Setup L A C z) (σ : egNL L A →* Equiv.Perm (Fin 6)) (hσ : Function.Surjective σ)
    (hA : A.subgroupOf (egNL L A) ≤ σ.ker) (hk : Nat.card σ.ker = 192) :
    CLayerDisjIso (egQD C) :=
  hHS (egQD C) hK (zt h) (orderOf_zt h) (centralizer_oddCore_equiv h σ hσ hA hk)

end CSide

end CFSG.EvenSporadicStandard.M24Std
