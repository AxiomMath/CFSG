module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTen

import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.HardMathSupport.Solomon.Proving.GLBCoreNormalizer
import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.StarQuot
import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.O98ThreeEleven
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenTrans
import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2T_Two

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineSettingGen

open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {M Q H E : Subgroup G} {p : ℕ}

theorem isElemAbelian_starImg_E_gen (h : NineSettingGen G M p Q H E 2) :
    CFSG.Open.IsElemAbelian p (starImg p H E) := by
  obtain ⟨-, hEQ, hE, -, -⟩ := h.stdE
  exact (CFSG.LocalAnalysis.AGL81TheoremCD.Section15.isElemAbelian_starImg_iff
    h.prime (hEQ.trans h.Q_le_H) (CFSG.Open.IsElemAbelian.isPGroup hE)).mpr hE

theorem card_starImg_E_gen (h : NineSettingGen G M p Q H E 2) :
    Nat.card (starImg p H E) = p ^ 2 := by
  obtain ⟨-, hEQ, hE, hEc, -⟩ := h.stdE
  rw [card_starImg_eq h.prime (hEQ.trans h.Q_le_H)
    (CFSG.Open.IsElemAbelian.isPGroup hE), hEc]

theorem two_le_pRank_starImg_E_gen (h : NineSettingGen G M p Q H E 2) :
    2 ≤ CFSG.Open.pRank p (starImg p H E) :=
  CFSG.SectionRank.le_pRank (p := p) h.prime.one_lt le_rfl
    (isElemAbelian_starImg_E_gen h) (by rw [card_starImg_E_gen h])

theorem rankThreeGamma_starImg_E_le_gen (h : NineSettingGen G M p Q H E 2) :
    CFSG.Open.rankThreeGamma 1 p (starImg p H E) ≤ starImg p H M := by
  obtain ⟨-, hEQ, hE, -, hΓ⟩ := h.stdE
  exact CFSG.LocalAnalysis.AGL81TheoremCD.Section15.rankThreeGamma_starImg_le
    (p := p) (k := 1) h.prime (hEQ.trans h.Q_le_H)
    (CFSG.Open.IsElemAbelian.isPGroup hE)
    (fun D hDE hD => inf_le_left.trans
      ((CFSG.HardMathSupport.Solomon.Proving.normalizer_le_glbCore hDE hD).trans hΓ))

theorem starImg_E_le_normalizer_gen (h : NineSettingGen G M p Q H E 2)
    {C : Subgroup (StarGroup p H)} (hC : CFSG.IsComponent C) (hCM : ¬ C ≤ starImg p H M) :
    starImg p H E ≤ Subgroup.normalizer (C : Set (StarGroup p H)) := by
  rcases CFSG.LocalAnalysis.AGL81TheoremCD.Section15.le_gamma_or_le_normalizer
    (X := StarGroup p H) (p := p) h.prime hC
    (CFSG.LocalAnalysis.RankThreeTheoremC.thc_dvd_card (p := p) h.prime
      (CFSG.LocalAnalysis.AGL81TheoremCD.Section15.pPrimeCore_starGroup (H := H) h.prime) hC)
    (isElemAbelian_starImg_E_gen h) (two_le_pRank_starImg_E_gen h) with hΓ | hN
  · exact absurd (hΓ.trans (rankThreeGamma_starImg_E_le_gen h)) hCM
  · exact hN

theorem not_le_centralizer_of_mem_starImg_E_gen (h : NineSettingGen G M p Q H E 2)
    {C : Subgroup (StarGroup p H)} (hCM : ¬ C ≤ starImg p H M) {e : StarGroup p H}
    (he : e ∈ starImg p H E) (he1 : e ≠ 1) :
    ¬ C ≤ Subgroup.centralizer ({e} : Set (StarGroup p H)) := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  intro hC
  have hep : e ^ p = 1 := (isElemAbelian_starImg_E_gen h).2 e he
  have hord : orderOf e = p := orderOf_eq_prime hep he1
  have hcard : Nat.card (Subgroup.zpowers e) = p ^ 1 := by
    rw [Nat.card_zpowers, hord, pow_one]
  have hrank : 1 ≤ CFSG.Open.pRank p (Subgroup.zpowers e) :=
    CFSG.SectionRank.le_pRank (p := p) h.prime.one_lt le_rfl
      (CFSG.Open.isElemAbelian_zpowers hep) hcard
  have hzE : Subgroup.zpowers e ≤ starImg p H E := Subgroup.zpowers_le.mpr he
  have hN := CFSG.HardMathSupport.Solomon.Proving.normalizer_le_glbCore
    (p := p) (k := 1) hzE hrank
  have hcent : Subgroup.centralizer ({e} : Set (StarGroup p H)) =
      Subgroup.centralizer (Subgroup.zpowers e : Set (StarGroup p H)) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  rw [hcent] at hC
  exact hCM (hC.trans ((Subgroup.centralizer_le_normalizer
    (Subgroup.zpowers e : Set (StarGroup p H))).trans
      (hN.trans (rankThreeGamma_starImg_E_le_gen h))))

end CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineSettingGen
