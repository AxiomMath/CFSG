module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTen

import CFSG.HardMathSupport.Solomon.Proving.GLBCoreNormalizer
import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.StarQuot
import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.O98ThreeEleven
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenTrans
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenLayer
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineEightB
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.O1217Structure
import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2T_Two

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineSettingGen

open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {M Q H E : Subgroup G}

theorem isElemAbelian_starImg_E (h : NineSettingGen G M 3 Q H E 2) :
    CFSG.Open.IsElemAbelian 3 (starImg 3 H E) := by
  obtain ⟨-, hEQ, hE, -, -⟩ := h.stdE
  exact (CFSG.LocalAnalysis.AGL81TheoremCD.Section15.isElemAbelian_starImg_iff
    Nat.prime_three (hEQ.trans h.Q_le_H) (CFSG.Open.IsElemAbelian.isPGroup hE)).mpr hE

theorem card_starImg_E (h : NineSettingGen G M 3 Q H E 2) : Nat.card (starImg 3 H E) = 9 := by
  obtain ⟨-, hEQ, hE, hEc, -⟩ := h.stdE
  rw [card_starImg_eq Nat.prime_three (hEQ.trans h.Q_le_H)
    (CFSG.Open.IsElemAbelian.isPGroup hE), hEc]
  norm_num

theorem two_le_pRank_starImg_E (h : NineSettingGen G M 3 Q H E 2) :
    2 ≤ CFSG.Open.pRank 3 (starImg 3 H E) :=
  CFSG.SectionRank.le_pRank (p := 3) (by norm_num) le_rfl
    (isElemAbelian_starImg_E h) (by rw [card_starImg_E h]; norm_num)

theorem rankThreeGamma_starImg_E_le (h : NineSettingGen G M 3 Q H E 2) :
    CFSG.Open.rankThreeGamma 1 3 (starImg 3 H E) ≤ starImg 3 H M := by
  obtain ⟨-, hEQ, hE, -, hΓ⟩ := h.stdE
  have hΓ' : CFSG.Open.rankThreeGamma 1 3 E ≤ M := hΓ
  exact CFSG.LocalAnalysis.AGL81TheoremCD.Section15.rankThreeGamma_starImg_le
    (p := 3) (k := 1) Nat.prime_three (hEQ.trans h.Q_le_H)
    (CFSG.Open.IsElemAbelian.isPGroup hE)
    (fun D hDE hD => inf_le_left.trans
      ((CFSG.HardMathSupport.Solomon.Proving.normalizer_le_glbCore hDE hD).trans hΓ'))

theorem starImg_E_le_normalizer (h : NineSettingGen G M 3 Q H E 2)
    {C : Subgroup (StarGroup 3 H)} (hC : CFSG.IsComponent C) (hCM : ¬ C ≤ starImg 3 H M) :
    starImg 3 H E ≤ Subgroup.normalizer (C : Set (StarGroup 3 H)) := by
  rcases CFSG.LocalAnalysis.AGL81TheoremCD.Section15.le_gamma_or_le_normalizer
    (X := StarGroup 3 H) (p := 3) Nat.prime_three hC
    (CFSG.LocalAnalysis.RankThreeTheoremC.thc_dvd_card (p := 3) Nat.prime_three
      (CFSG.LocalAnalysis.AGL81TheoremCD.Section15.pPrimeCore_starGroup Nat.prime_three) hC)
    (isElemAbelian_starImg_E h) (two_le_pRank_starImg_E h) with hΓ | hN
  · exact absurd (hΓ.trans (rankThreeGamma_starImg_E_le h)) hCM
  · exact hN

theorem not_le_centralizer_of_mem_starImg_E (h : NineSettingGen G M 3 Q H E 2)
    {C : Subgroup (StarGroup 3 H)} (hCM : ¬ C ≤ starImg 3 H M) {e : StarGroup 3 H}
    (he : e ∈ starImg 3 H E) (he1 : e ≠ 1) :
    ¬ C ≤ Subgroup.centralizer ({e} : Set (StarGroup 3 H)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro hC
  have he3 : e ^ 3 = 1 := (isElemAbelian_starImg_E h).2 e he
  have hord : orderOf e = 3 := orderOf_eq_prime he3 he1
  have hcard : Nat.card (Subgroup.zpowers e) = 3 ^ 1 := by
    rw [Nat.card_zpowers, hord, pow_one]
  have hrank : 1 ≤ CFSG.Open.pRank 3 (Subgroup.zpowers e) :=
    CFSG.SectionRank.le_pRank (p := 3) (by norm_num) le_rfl
      (CFSG.Open.isElemAbelian_zpowers he3) hcard
  have hzE : Subgroup.zpowers e ≤ starImg 3 H E := Subgroup.zpowers_le.mpr he
  have hN := CFSG.HardMathSupport.Solomon.Proving.normalizer_le_glbCore
    (p := 3) (k := 1) hzE hrank
  have hcent : Subgroup.centralizer ({e} : Set (StarGroup 3 H)) =
      Subgroup.centralizer (Subgroup.zpowers e : Set (StarGroup 3 H)) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  rw [hcent] at hC
  exact hCM (hC.trans ((Subgroup.centralizer_le_normalizer
    (Subgroup.zpowers e : Set (StarGroup 3 H))).trans
      (hN.trans (rankThreeGamma_starImg_E_le h))))

theorem E_le_normalizer_of_isPComponentIn (h : NineSettingGen G M 3 Q H E 2)
    {J : Subgroup G} (hJ : IsPComponentIn 3 J H) (hJM : ¬ J ≤ M) :
    E ≤ Subgroup.normalizer (J : Set G) := by
  obtain ⟨-, hEQ, -, -, -⟩ := h.stdE
  have hEH : E ≤ H := hEQ.trans h.Q_le_H
  have hC : CFSG.IsComponent (starImg 3 H J) := isComponent_starImg hJ
  have hCM : ¬ starImg 3 H J ≤ starImg 3 H M :=
    fun hle => hJM ((h.toCore.le_iff_starImg_le hJ.1).mpr hle)
  have hEN := starImg_E_le_normalizer h hC hCM
  intro y hy
  let yH : ↥H := ⟨y, hEH hy⟩
  let ybar : StarGroup 3 H := QuotientGroup.mk' (primeComplementCore (G := ↥H) 3) yH
  have hybar : ybar ∈ starImg 3 H E :=
    Subgroup.mem_map.mpr ⟨yH, Subgroup.mem_subgroupOf.mpr hy, rfl⟩
  have hyN : ybar ∈ Subgroup.normalizer (starImg 3 H J : Set (StarGroup 3 H)) := hEN hybar
  have hmap : (starImg 3 H J).map (MulAut.conj ybar).toMonoidHom = starImg 3 H J :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hyN
  have hstar : starImg 3 H (J.map (MulAut.conj y).toMonoidHom) = starImg 3 H J := by
    calc starImg 3 H (J.map (MulAut.conj y).toMonoidHom)
        = (starImg 3 H J).map (MulAut.conj ybar).toMonoidHom := by
          simpa [ybar] using starImg_map_conj 3 H J yH
      _ = starImg 3 H J := hmap
  have hconj : IsPComponentIn 3 (J.map (MulAut.conj y).toMonoidHom) H :=
    isPComponentIn_conj hJ (hEH hy)
  have hEq : J.map (MulAut.conj y).toMonoidHom = J :=
    eq_of_starImg_eq Nat.prime_three hconj hJ hstar
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr hEq

end CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineSettingGen
