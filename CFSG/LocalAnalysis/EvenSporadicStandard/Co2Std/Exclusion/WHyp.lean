module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Co2Std.Exclusion.E2
public import CFSG.LocalAnalysis.EvenSporadicStandard.Co2Std.Exclusion.E3
public import CFSG.LocalAnalysis.EvenSporadicStandard.Co2Std.Exclusion.Split

public section

namespace CFSG.EvenSporadicStandard.Co2Std.Exclusion

open Subgroup

structure WHyp (G : Type) [Group G] [Finite G] (L A T : Subgroup G) (z t : G)
    (W W₁ W₂ : Subgroup G) : Prop where
  hyp : Hyp G L A T z t
  e2 : E2Facts L A z
  e3 : E3Facts A z W
  w : WFacts L A z W₁ W₂
  sup_eq : W₁ ⊔ W₂ = W

theorem Hyp.exists_wHyp {G : Type} [Group G] [Finite G] {L A T : Subgroup G} {z t : G}
    (h : Hyp G L A T z t) : ∃ W W₁ W₂ : Subgroup G, WHyp G L A T z t W W₁ W₂ := by
  obtain ⟨W, h3⟩ := h.exists_e3Facts h.e2Facts
  obtain ⟨W₁, W₂, hw, hsup⟩ :=
    h.exists_wFacts h.e2Facts h3 (h.isElementaryAbelian_of_e3Facts h.e2Facts h3)
  exact ⟨W, W₁, W₂, ⟨h, h.e2Facts, h3, hw, hsup⟩⟩

end CFSG.EvenSporadicStandard.Co2Std.Exclusion
