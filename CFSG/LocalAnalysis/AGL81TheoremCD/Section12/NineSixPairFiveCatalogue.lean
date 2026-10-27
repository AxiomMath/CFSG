module

public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineCatFiveMain
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTen
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineSixStarEGen
import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineTenThreeGen
import CFSG.LocalAnalysis.RankThreeUC.AGL81CZBridge
import CFSG.LocalAnalysis.GLTheoremB.Prop95Iii
import CFSG.RankThree.PartOne.S8.ResidualBound
import CFSG.LocalAnalysis.UniquenessCase.UC6K36Comp
import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.StarQuot
import CFSG.HardMathSupport.Solomon.Proving.GLBCoreNormalizer

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open Subgroup CFSG.LocalAnalysis.RankThreeUC.AGL81C

theorem map_gammaOver_subgroupOf_le {Y : Type} [Group Y] [Finite Y] {p : ℕ} (hp : p.Prime)
    (N R T : Subgroup Y) :
    (gammaOver 1 p (R.subgroupOf N) (T.subgroupOf N)).map N.subtype ≤
      CFSG.Open.rankThreeGamma 1 p R := by
  rw [Subgroup.map_le_iff_le_comap]
  unfold gammaOver
  refine iSup_le fun F => iSup_le fun hF => iSup_le fun hk => ?_
  intro x hx
  rw [Subgroup.mem_inf] at hx
  rw [Subgroup.mem_comap]
  obtain ⟨hx1, -⟩ := hx
  have hFR : F.map N.subtype ≤ R := by
    rintro y ⟨f, hf, rfl⟩
    exact hF hf
  have hxN : (x : Y) ∈ Subgroup.normalizer (F.map N.subtype : Set Y) :=
    Subgroup.le_normalizer_map (f := N.subtype) (H := F)
      (Subgroup.mem_map_of_mem N.subtype hx1)
  have hk' : 1 ≤ CFSG.Open.pRank p (F.map N.subtype) :=
    hk.trans (CFSG.SectionRank.pRank_le_map hp.one_lt N.subtype N.subtype_injective F)
  exact CFSG.HardMathSupport.Solomon.Proving.normalizer_le_glbCore hFR hk' hxN

theorem pPrimeCore_eq_bot_of_isComponent_of_prime {Y : Type} [Group Y] [Finite Y] {p : ℕ}
    (hp : p.Prime) (hY : CFSG.pPrimeCore p Y = ⊥) {C : Subgroup Y} (hC : CFSG.IsComponent C) :
    CFSG.pPrimeCore p ↥C = ⊥ := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h := CFSG.LocalAnalysis.UniquenessCase.UCK.map_pPrimeCore_le_of_isSubnormal_of_prime
    (s := p) hC.2
  rw [hY, le_bot_iff] at h
  exact (Subgroup.map_eq_bot_iff_of_injective (CFSG.pPrimeCore p ↥C)
    C.subtype_injective).mp h

variable {G : Type} [Group G] [Finite G] {M Q H E : Subgroup G} {p : ℕ}

theorem isKGroupCat_starGroup_of_nineSettingGen
    (hbridge : CFSG.RankThree.PartOne.TauCetiCatalogBridge) {k : ℕ}
    (h : NineSettingGen G M p Q H E k) : CFSG.SectionRank.IsKGroupCat (StarGroup p H) :=
  CFSG.RankThree.PartOne.isKGroupCat_of_isKGroup hbridge
    (CFSG.LocalAnalysis.GLTheoremB.Prop95Parts.isKGroup_catalog_of_open (h.isKGroup_quotient p))

theorem kGroupLowRank24_12_subgroupOf_normalizer
    (hCat : CFSG.LocalAnalysis.AGL81I.Section3.Catalogue24_12Five)
    (hbridge : CFSG.RankThree.PartOne.TauCetiCatalogBridge)
    (h : NineSettingGen G M p Q H E 2) (hH2 : H ∈ H2Fam M Q)
    (hσ : p ∉ CFSG.LocalAnalysis.RankThreeUC.S15.sigmaM G M) (hp5 : 5 ≤ p)
    {C : Subgroup (StarGroup p H)} (hC : CFSG.IsComponent C) (hCM : ¬ C ≤ starImg p H M) :
    CFSG.LocalAnalysis.AGL81I.Section3.KGroupLowRank24_12 p
      ↥(C.subgroupOf (Subgroup.normalizer (C : Set (StarGroup p H)))) := by
  let N : Subgroup (StarGroup p H) := Subgroup.normalizer (C : Set (StarGroup p H))
  let e := Subgroup.subgroupOfEquivOfLe (Subgroup.le_normalizer (H := C))
  have hEN : starImg p H E ≤ N := h.starImg_E_le_normalizer_gen hC hCM
  have hO : CFSG.pPrimeCore p ↥(C.subgroupOf N) = ⊥ := by
    have hC0 : CFSG.pPrimeCore p ↥C = ⊥ :=
      pPrimeCore_eq_bot_of_isComponent_of_prime h.prime
        (CFSG.LocalAnalysis.AGL81TheoremCD.Section15.pPrimeCore_starGroup (H := H) h.prime) hC
    have hm := CFSG.pPrimeCore_map_iso p e
    rw [hC0] at hm
    exact (Subgroup.map_eq_bot_iff_of_injective
      (CFSG.pPrimeCore p ↥(C.subgroupOf N)) e.injective).mp hm
  have hK : CFSG.SectionRank.IsKGroupCat ↥(C.subgroupOf N) :=
    ((isKGroupCat_starGroup_of_nineSettingGen hbridge h).subgroup N).subgroup (C.subgroupOf N)
  have hE : IsElemAbelian p ((starImg p H E).subgroupOf N) :=
    (h.isElemAbelian_starImg_E_gen).subgroupOf N
  have hEcard : Nat.card ((starImg p H E).subgroupOf N) = p ^ 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEN).toEquiv, h.card_starImg_E_gen]
  have htop : CFSG.Open.pRank p (⊤ : Subgroup ↥N) ≤
      CFSG.Open.pRank p (⊤ : Subgroup (StarGroup p H)) := by
    have hm := CFSG.SectionRank.pRank_le_map h.prime.one_lt N.subtype N.subtype_injective
      (⊤ : Subgroup ↥N)
    have hmap : (⊤ : Subgroup ↥N).map N.subtype = N := by
      simpa using Subgroup.subgroupOf_map_subtype (⊤ : Subgroup (StarGroup p H)) N
    rw [hmap] at hm
    exact hm.trans (CFSG.SectionRank.pRank_mono h.prime.one_lt le_top)
  have hrank : CFSG.Open.pRank p ((C.subgroupOf N) ⊔ ((starImg p H E).subgroupOf N)) ≤ 3 :=
    (CFSG.SectionRank.pRank_mono h.prime.one_lt le_top).trans
      (htop.trans (h.pRank_star_le_three hH2 hσ))
  have hΓ : ¬ (C.subgroupOf N) ≤ gammaOver 1 p ((starImg p H E).subgroupOf N) (C.subgroupOf N) := by
    intro hle
    apply hCM
    calc C = (C.subgroupOf N).map N.subtype :=
          (Subgroup.map_subgroupOf_eq_of_le (Subgroup.le_normalizer (H := C))).symm
      _ ≤ (gammaOver 1 p ((starImg p H E).subgroupOf N) (C.subgroupOf N)).map N.subtype :=
          Subgroup.map_mono hle
      _ ≤ CFSG.Open.rankThreeGamma 1 p (starImg p H E) :=
          map_gammaOver_subgroupOf_le h.prime N (starImg p H E) C
      _ ≤ starImg p H M := h.rankThreeGamma_starImg_E_le_gen
  exact hCat ↥N (C.subgroupOf N) ((starImg p H E).subgroupOf N) p h.prime hp5
    (CFSG.IsQuasisimple.of_mulEquiv e hC.1) hO hK Subgroup.normal_in_normalizer hE hEcard
    hrank hΓ

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12