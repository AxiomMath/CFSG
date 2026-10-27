module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenThree
public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.Base
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenLayer
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenListNormal

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.LocalAnalysis.RankThreeUC.S15 Subgroup

variable {G : Type} [Group G] [Finite G] {M : Subgroup G} {p : ℕ} {Q H E : Subgroup G} {k : ℕ}

namespace NineSettingGen

theorem pRank_star_le_three (h : NineSettingGen G M p Q H E k) (hH2 : H ∈ H2Fam M Q)
    (hp : p ∉ sigmaM G M) : CFSG.Open.pRank p (⊤ : Subgroup (StarGroup p H)) ≤ 3 := by
  rw [← starImg_self p H, pRank_starImg_eq h.prime le_rfl]
  exact (h.pRank_le_of_mem_H2Fam hH2 hp).1

theorem pRank_pCore_star_le_three (h : NineSettingGen G M p Q H E k) (hH2 : H ∈ H2Fam M Q)
    (hp : p ∉ sigmaM G M) : CFSG.Open.pRank p (CFSG.pCore p (StarGroup p H)) ≤ 3 :=
  (CFSG.SectionRank.pRank_mono h.prime.one_lt le_top).trans
    (h.pRank_star_le_three hH2 hp)

theorem sixThreeOneList_of_layer_eq_bot (h63 : SixThreeOne) (h : NineSettingGen G M p Q H E k)
    (hH2 : H ∈ H2Fam M Q) (hp : p ∉ sigmaM G M) (hL : pLayerIn p H = ⊥) :
    SixThreeOneList p
      ↥(oPPrimeHull p (⊤ : Subgroup (StarGroup p H ⧸ CFSG.pCore p (StarGroup p H)))) :=
  h63 p h.prime h.ne_two (StarGroup p H)
    (centralizer_pCore_le_of_layer_eq_bot h.prime H ((pLayerIn_eq_bot_iff h.prime H).mp hL))
    (h.pRank_pCore_star_le_three hH2 hp)
    (h.pRank_star_le_three hH2 hp)

theorem exists_orderOf_map_kStar (h : NineSettingGen G M p Q H E 2) (hp : p ∉ sigmaM G M)
    (hU : NineNineOne M p) (hL : pLayerIn p H ≤ M) :
    ∃ x ∈ (kStar p M H).map (QuotientGroup.mk' (CFSG.pCore p (StarGroup p H))), orderOf x = p := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  have hEk : E ≤ kSub p M H :=
    le_kSub_of_le h.prime hL (h.stdE.2.1.trans h.Q_le_H) h.stdE.2.2.1.2
  have hstar_le : starImg p H E ≤ kStar p M H := by
    rw [kStar_eq_starImg p M H]
    exact Subgroup.map_mono (Subgroup.comap_mono hEk)
  obtain ⟨e, heE, heR⟩ := SetLike.not_le_iff_exists.mp (h.not_starImg_le_pCore hp hU)
  change e ∈ (E.subgroupOf H).map
    (QuotientGroup.mk' (primeComplementCore (G := ↥H) p)) at heE
  obtain ⟨a, ha, hae⟩ := Subgroup.mem_map.mp heE
  have hap : a ^ p = 1 :=
    Subtype.ext (h.stdE.2.2.1.2 (a : G) (Subgroup.mem_subgroupOf.mp ha))
  have hep : e ^ p = 1 := by rw [← hae, ← map_pow, hap, map_one]
  refine ⟨QuotientGroup.mk' (CFSG.pCore p (StarGroup p H)) e,
    Subgroup.mem_map_of_mem _ (hstar_le heE), ?_⟩
  refine orderOf_eq_prime (by rw [← map_pow, hep, map_one]) (fun h1 => heR ?_)
  exact (QuotientGroup.eq_one_iff e).mp h1

theorem nineTenThreeCorrected (h63 : SixThreeOne) (h : NineSettingGen G M p Q H E 2)
    (hH2 : H ∈ H2Fam M Q) (hp : p ∉ sigmaM G M) (hU : NineNineOne M p)
    (hL : pLayerIn p H = ⊥) : NineTenThreeCorrected p M H := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  have hLM : pLayerIn p H ≤ M := by rw [hL]; exact bot_le
  haveI hKnorm : (kStar p M H).Normal := kStar_normal_of_le hLM
  haveI hNnorm : ((kStar p M H).map
      (QuotientGroup.mk' (CFSG.pCore p (StarGroup p H)))).Normal :=
    hKnorm.map _ (QuotientGroup.mk'_surjective _)
  obtain ⟨hlist, hcard⟩ :=
    sixThreeOneList_of_normal h.prime h.ne_two
      (h.sixThreeOneList_of_layer_eq_bot h63 hH2 hp hL)
      (oPPrimeHull_map_kStar h.prime hLM)
      (h.exists_orderOf_map_kStar hp hU hLM)
  obtain ⟨e⟩ := nonempty_quot_pCore_mulEquiv_map (p := p) (kStar p M H)
  exact ⟨SixThreeOneList.of_mulEquiv e.symm hlist,
    fun h1 => hcard ((Nat.card_congr e.toEquiv).symm.trans h1)⟩

end NineSettingGen

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
