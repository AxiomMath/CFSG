module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.H2.StructA

public section

namespace CFSG.EvenSporadicStandard.HSStd.InvCent

open Subgroup CFSG CFSG.EvenSporadicStandard.SolomonRed

namespace H2Cfg

variable {G : Type*} [Group G] {t v : G} {J : Subgroup G}

theorem exists_component_eq_layer [Finite G] (cfg : H2Cfg G t v J) (hF : fittingSubgroup G = ⊥)
    (hle : layer G ⊓ centralizer ({t} : Set G) ≤ kleinV t v) :
    ∃ L : Subgroup G, IsComponent L ∧ layer G = L := by
  obtain ⟨L₀, hL₀⟩ := exists_component hF ⟨t, cfg.t_ne_one⟩
  have hV_le : ∀ K : Subgroup G, IsComponent K → kleinV t v ≤ K := fun K hK =>
    kleinV_le_of_inf_le cfg hF hK
      ((inf_le_inf_right (centralizer ({t} : Set G))
        (CFSG.LocalCores.component_le_layer hK)).trans hle)
  have hEq : ∀ K : Subgroup G, IsComponent K → K = L₀ := by
    intro K hK
    by_contra hne
    have hbot : K ⊓ L₀ = ⊥ := component_inf_eq_bot hF hK hL₀ hne
    have hKV : kleinV t v ≤ K ⊓ L₀ := le_inf (hV_le K hK) (hV_le L₀ hL₀)
    rw [hbot] at hKV
    exact cfg.kleinV_ne_bot (le_bot_iff.mp hKV)
  exact ⟨L₀, hL₀, le_antisymm (by
    rw [CFSG.layer.eq_sSup]
    exact sSup_le fun K hK => le_of_eq (hEq K hK)) (CFSG.LocalCores.component_le_layer hL₀)⟩

end H2Cfg

end CFSG.EvenSporadicStandard.HSStd.InvCent
