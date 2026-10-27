module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.Base
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenLayer

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.LocalAnalysis.RankThreeUC.S15 Subgroup

variable {G : Type} [Group G] [Finite G] {M : Subgroup G} {p : ℕ} {Q H E : Subgroup G} {k : ℕ}

namespace NineSettingGen

theorem le_iff_starImg_le (h : NineSettingGen G M p Q H E k) {A : Subgroup G} (hAH : A ≤ H) :
    A ≤ M ↔ starImg p H A ≤ starImg p H M := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  constructor
  · intro hAM
    exact Subgroup.map_mono (Subgroup.comap_mono hAM)
  · intro hAM
    have h1 : A.subgroupOf H ≤ M.subgroupOf H ⊔ CFSG.pPrimeCore p ↥H := by
      have h2 : (A.subgroupOf H).map
            (QuotientGroup.mk' (primeComplementCore (G := ↥H) p)) ≤
          (M.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := ↥H) p)) := hAM
      have h3 := Subgroup.map_le_iff_le_comap.mp h2
      rwa [Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at h3
    calc A = (A.subgroupOf H).map H.subtype := (Subgroup.map_subgroupOf_eq_of_le hAH).symm
      _ ≤ (M.subgroupOf H ⊔ CFSG.pPrimeCore p ↥H).map H.subtype := Subgroup.map_mono h1
      _ = (M.subgroupOf H).map H.subtype ⊔ (CFSG.pPrimeCore p ↥H).map H.subtype := by
            rw [Subgroup.map_sup]
      _ ≤ M := by
            refine sup_le ?_ ?_
            · rw [Subgroup.subgroupOf_map_subtype]
              exact inf_le_left
            · change (primeComplementCore (G := ↥H) p).map H.subtype ≤ M
              rw [← nineTenGen_relPPrimeCore_eq_map h.prime H]
              exact h.relPPrimeCore_le

theorem pLayerIn_le_iff (h : NineSettingGen G M p Q H E k) :
    pLayerIn p H ≤ M ↔ CFSG.layer (StarGroup p H) ≤ starImg p H M := by
  have hle := h.le_iff_starImg_le (A := pLayerIn p H)
    (Subgroup.map_subtype_le (CFSG.pLayer ↥H p))
  rw [hle, starImg_pLayerIn h.prime]


end NineSettingGen

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
