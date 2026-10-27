module

public import CFSG.GH74.GLS.Basic

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup

theorem catalog_center_quotient_of_kProper {G : Type} [Group G] [Finite G]
    (hK : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G) {Hh : Subgroup G} (hHh : Hh ≠ ⊤)
    (hq : CFSG.IsQuasisimple ↥Hh) : CFSG.Blueprint.Catalog (↥Hh ⧸ center ↥Hh) := by
  haveI : IsSimpleGroup (↥Hh ⧸ center ↥Hh) := hq.2.1
  have hX : CFSG.SectionRank.IsKGroupCat ↥Hh := CFSG.GH74.GLS.isKGroupNative_of_kProper hK hHh
  exact CFSG.SectionRank.catalog_of_isKGroupCat_of_surjective (hX.quotient (center ↥Hh)) ⊤
    (⊤ : Subgroup (↥Hh ⧸ center ↥Hh)).subtype fun y => ⟨⟨y, mem_top y⟩, rfl⟩

end CFSG.OddStandard.HigherRank.YamadaG23
