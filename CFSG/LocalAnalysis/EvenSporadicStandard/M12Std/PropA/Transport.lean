module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.PropA.TransportEls

public section

namespace CFSG.EvenSporadicStandard.M12Std.PropA

open Subgroup

variable {G P : Type*} [Group G] [Group P] {L : Subgroup G} {t x : G} {K D : Subgroup P}
  {t₀ x₀ : P} {ι : ↥(centralizer ({t} : Set G)) →* P}

theorem IsEmb.facts (hE : IsEmb L t x K D t₀ x₀ ι) (M : Model K D t₀ x₀) : Facts L t x :=
  ⟨hE.card_J M, hE.card_Cx M, hE.J_le, hE.J_normal M, hE.J_center M, hE.card_Y M, hE.G3 M,
    hE.G5 M, hE.G1 M, hE.G2 M⟩

end CFSG.EvenSporadicStandard.M12Std.PropA
