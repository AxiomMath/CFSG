module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenFiveMain
public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineTenRankRGen
public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineTenSingleGen
public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineTenKerQuotGen
public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineTenLayerGen
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenTrans

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open Subgroup

namespace NineSettingGen

open CFSG.LocalAnalysis.RankThreeUC.S15

variable {G : Type} [Group G] [Finite G] {M : Subgroup G} {p : ℕ} {Q H E : Subgroup G}

theorem nineTenTwo_five (h72 : KFactOmegaNotCentral) (h2 : KFactCenterRankTwo)
    (h5c : KFactCenterRankFive) (h714 : SevenOneFourSplit) (h661 : SixSixOneRank)
    (h : NineSettingGen G M p Q H E 2) (hH2 : H ∈ H2Fam M Q) (hp : p ∉ sigmaM G M)
    (hU : NineNineOne M p) (hQ : CFSG.ABGLocalTools.IsSylowOf p Q H)
    (hY : ¬ centralizer (CFSG.layer (StarGroup p H) : Set (StarGroup p H)) ≤ starImg p H M)
    (hL : pLayerIn p H ≠ ⊥) (hp3 : p ≠ 3) :
    pLayerIn p H ≤ M ∧ NineTenTwo p M H E := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  have hR : 2 ≤ CFSG.Open.pRank p (CFSG.pCore p (StarGroup p H)) :=
    h.two_le_pRank_pCore hU hQ hY
  obtain ⟨hR2, J, hJ, _, hlayer, hpc, hJ5⟩ :=
    h.single_component h72 h2 h5c hH2 hp hR hL
  let L : Subgroup (StarGroup p H) := CFSG.layer (StarGroup p H)
  haveI hLchar : L.Characteristic := CFSG.LocalCores.layer_characteristic
  haveI hLn : L.Normal := inferInstance
  have hLc : CFSG.IsComponent L := by
    change CFSG.IsComponent (CFSG.layer (StarGroup p H))
    rw [hlayer]
    exact hJ
  have hLq : CFSG.IsQuasisimple ↥L := hLc.1
  have hp2le : 2 ≤ p := h.prime.two_le
  have hLrk : CFSG.Open.pRank p L = 1 := by
    change CFSG.Open.pRank p (CFSG.layer (StarGroup p H)) = 1
    rw [hlayer]
    rcases hpc with h1 | ⟨hJ2, hdvd⟩
    · exact h1
    · exfalso
      have hp5le : 5 ≤ p := by
        rcases h.prime.odd_of_ne_two h.ne_two with ⟨k, hk⟩
        omega
      have h3 := h5c (StarGroup p H) h.isKGroup_star J hJ p h.prime hp5le hdvd
      omega
  have hp3' : 3 < p := by
    rcases h.prime.odd_of_ne_two h.ne_two with ⟨k, hk⟩
    omega
  obtain ⟨W, hW⟩ :=
    h714 (StarGroup p H) h.isKGroup_star p h.prime h.ne_two L hLc hLn hLrk
  have hW' : IsSplitCover p L W := hW
  have hZ : ∀ z ∈ L, z ∈ centralizer (L : Set (StarGroup p H)) → z ^ p = 1 → z = 1 := by
    intro z hzL hzC hzp
    by_contra hz1
    have hzord : orderOf z = p := orderOf_eq_prime hzp hz1
    have hzcent : (⟨z, hzL⟩ : ↥L) ∈ center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro w
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hzC w w.2)
    have hzord' : orderOf (⟨⟨z, hzL⟩, hzcent⟩ : center ↥L) = p := by
      simpa using hzord
    have hdvd : p ∣ Nat.card (center ↥L) := by
      simpa only [hzord'] using
        orderOf_dvd_natCard (⟨⟨z, hzL⟩, hzcent⟩ : center ↥L)
    exact (not_dvd_card_center_of_pRank_eq_one h72 h.isKGroup_star hLc h.prime h.ne_two
      hLrk) hdvd
  have hRY : CFSG.pCore p (StarGroup p H) ≤ centralizer (L : Set (StarGroup p H)) :=
    pCore_le_centralizer_layer h.prime H
  have hYR : centralizer (L : Set (StarGroup p H)) ⊓
      centralizer (CFSG.pCore p (StarGroup p H) : Set (StarGroup p H)) ≤
        CFSG.pCore p (StarGroup p H) := by
    rw [← cStarL_eq_centralizer_layer h.prime H]
    exact cStarL_inf_centralizer_le_pCore h.prime H
  have hrk : CFSG.Open.pRank p (⊤ : Subgroup (StarGroup p H)) ≤ 3 :=
    h.pRank_star_le_three hH2 hp
  have hrkL : CFSG.Open.pRank p L ≤ 1 := hLrk.le
  have hEH : E ≤ H := h.stdE.2.1.trans h.Q_le_H
  have hEsub : CFSG.Open.IsElemAbelian p (E.subgroupOf H) :=
    CFSG.Open.IsElemAbelian.comap h.stdE.2.2.1 (f := H.subtype) H.subtype_injective
  have hEstar : CFSG.Open.IsElemAbelian p (starImg p H E) :=
    CFSG.SectionRank.isElemAbelian_map hEsub
      (QuotientGroup.mk' (CFSG.RankThreeCoreUniqueness.Helpers.primeComplementCore (G := ↥H) p))
  have hEp : IsPGroup p E := fun x => ⟨1, by
    apply Subtype.ext
    simpa using h.stdE.2.2.1.2 (x : G) x.2⟩
  have hEcstar : Nat.card (starImg p H E) = p ^ 2 := by
    rw [card_starImg_eq h.prime hEH hEp, h.stdE.2.2.2.1]
  obtain ⟨h1, h2, x, hxE, hxY, hx1⟩ :=
    hW'.five_core h661 h.prime hp3' hLn hZ hRY hYR hrk hrkL hLq hEstar hEcstar
      (fun U h₁ h₂ h₃ => h.not_starImg_le_of_normal hU hQ hY h₁ h₂ h₃)
  have hLcent : L ≤ centralizer (Subgroup.zpowers x : Set (StarGroup p H)) :=
    Subgroup.le_centralizer_iff.mpr (Subgroup.zpowers_le.mpr hxY)
  have hLstar : L ≤ starImg p H M :=
    hLcent.trans (h.centralizer_le_of_mem_starImg hxE hx1 (Subgroup.mem_zpowers x))
  have hLM : pLayerIn p H ≤ M := h.pLayerIn_le_iff.mpr hLstar
  have hpLayer : CFSG.Open.pRank p (pLayerIn p H) = 1 := by
    have hpr : CFSG.Open.pRank p (starImg p H (pLayerIn p H)) =
        CFSG.Open.pRank p (pLayerIn p H) :=
      pRank_starImg_eq h.prime (Subgroup.map_subtype_le (CFSG.pLayer ↥H p))
    rw [← hpr, starImg_pLayerIn h.prime H]
    exact hLrk
  refine ⟨hLM, Or.inr (Or.inl ⟨hp3', hR2, hpLayer, ?_, ?_⟩)⟩
  · rw [starImg_pLayerIn h.prime H, cStarL_eq_centralizer_layer h.prime H]
    exact h1
  · rw [cStarL_eq_centralizer_layer h.prime H]
    exact h2

end NineSettingGen

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
