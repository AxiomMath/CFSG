module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.H2.StructI
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.H2.StructII

public section

namespace CFSG.EvenSporadicStandard.HSStd.InvCent

open Subgroup CFSG CFSG.EvenSporadicStandard.SolomonRed

namespace H2Cfg

variable {G : Type*} [Group G] {t v : G} {J : Subgroup G}

theorem struct [Finite G] (cfg : H2Cfg G t v J) (hF : fittingSubgroup G = ⊥) :
    (∃ L : Subgroup G, IsComponent L ∧ layer G = L) ∨ ∃ S₁ : Subgroup G, H2Two G t v J S₁ := by
  have hLc : (layer G).Characteristic := CFSG.LocalCores.layer_characteristic
  have hLn : (layer G).Normal := inferInstance
  rcases cfg.le_kleinV_or_derived_le (N := layer G ⊓ centralizer ({t} : Set G)) inf_le_right
      (fun c hc x hx => ⟨hLn.conj_mem x hx.1 c, (centralizer ({t} : Set G)).mul_mem
        ((centralizer ({t} : Set G)).mul_mem hc hx.2) ((centralizer ({t} : Set G)).inv_mem hc)⟩)
    with h | h
  · exact Or.inl (cfg.exists_component_eq_layer hF h)
  · exact cfg.struct_of_derived_le_layer hF (h.trans inf_le_left)

end H2Cfg

end CFSG.EvenSporadicStandard.HSStd.InvCent
