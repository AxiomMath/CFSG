module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineTenCentGen
public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineTenSingleGen
public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineTenOneIGen

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.LocalAnalysis.RankThreeUC.S15 Subgroup

namespace NineSettingGen

variable {G : Type} [Group G] [Finite G] {M : Subgroup G} {p : ℕ} {Q H E : Subgroup G} {k : ℕ}

theorem kStar_eq_of_forall_isComponent_iff (h : NineSettingGen G M p Q H E k)
    (hL : ¬ pLayerIn p H ≤ M) {J : Subgroup (StarGroup p H)}
    (hJu : ∀ D : Subgroup (StarGroup p H), CFSG.IsComponent D ↔ D = J) : kStar p M H = J := by
  have hJM : ¬ J ≤ starImg p H M := by
    intro hJ
    have hlayer : CFSG.layer (StarGroup p H) ≤ starImg p H M := by
      rw [layer_eq_of_forall_isComponent_iff hJu]
      exact hJ
    exact hL (h.pLayerIn_le_iff.mpr hlayer)
  rw [h.kStar_eq_sSup_of_not_le hL]
  have hset : {C : Subgroup (StarGroup p H) |
      CFSG.IsComponent C ∧ ¬ C ≤ starImg p H M} = {J} := by
    ext C
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hC, -⟩
      exact (hJu C).mp hC
    · intro hCJ
      rw [hCJ]
      exact ⟨(hJu J).mpr rfl, hJM⟩
  rw [hset, sSup_singleton]

section Certified

theorem nineTenTwo_three (h713 : SevenOneThree) (hI : NineTenInputs)
    (h72 : KFactOmegaNotCentral) (h2 : KFactCenterRankTwo) (h5c : KFactCenterRankFive)
    (h : NineSettingGen G M 3 Q H E 2) (hH2 : H ∈ H2Fam M Q) (hp : 3 ∉ sigmaM G M)
    (hU : NineNineOne M 3) (hQ : CFSG.ABGLocalTools.IsSylowOf 3 Q H)
    (hNQ : normalizer (Q : Set G) ≤ M)
    (hQN : starImg 3 H Q ≤ compNormalizer (StarGroup 3 H))
    (hR : 2 ≤ CFSG.Open.pRank 3 (CFSG.pCore 3 (StarGroup 3 H)))
    (hL0 : pLayerIn 3 H ≠ ⊥) (hL : pLayerIn 3 H ≤ M) : NineTenTwo 3 M H E := by
  obtain ⟨hR2, J, hJ, hJu, hlay, hJr, -⟩ :=
    h.single_component h72 h2 h5c hH2 hp hR hL0
  have hstar : starImg 3 H (pLayerIn 3 H) = J :=
    (starImg_pLayerIn Nat.prime_three H).trans hlay
  refine Or.inr (Or.inr ⟨rfl, ?_, hR2, ?_, ?_⟩)
  · rw [hstar]
    rcases hJr with h1 | ⟨h2', -⟩
    · omega
    · omega
  · rw [hstar]
    exact hJ.1
  · exact h.isPSLType_oPPrimeHull_quotKer_of_le h713 hI hH2 hp hU hQ hNQ hQN hL hR2.le

theorem nineTenOne_three (h63 : NineSixThree) (h72 : KFactOmegaNotCentral)
    (h2 : KFactCenterRankTwo) (h5c : KFactCenterRankFive)
    (h : NineSettingGen G M 3 Q H E 2) (hH2 : H ∈ H2Fam M Q) (hp : 3 ∉ sigmaM G M)
    (hR : 2 ≤ CFSG.Open.pRank 3 (CFSG.pCore 3 (StarGroup 3 H)))
    (hY : ¬ centralizer (CFSG.layer (StarGroup 3 H) : Set (StarGroup 3 H)) ≤ starImg 3 H M)
    (hL : ¬ pLayerIn 3 H ≤ M) : NineTenOne 3 M H := by
  have hL0 : pLayerIn 3 H ≠ ⊥ := fun hbot => hL (by rw [hbot]; exact bot_le)
  obtain ⟨hR2, J, hJ, hJu, hlay, hJr, -⟩ :=
    h.single_component h72 h2 h5c hH2 hp hR hL0
  have hK : kStar 3 M H = J := h.kStar_eq_of_forall_isComponent_iff hL hJu
  have hXs : starImg 3 H (xSub 3 M H) =
      centralizer (CFSG.layer (StarGroup 3 H) : Set (StarGroup 3 H)) := by
    rw [starImg_xSub, hK, ← hlay]
  have hxH : xSub 3 M H ≤ H := by
    unfold xSub CFSG.AGLEmbedding.d1PlusCore
    exact Subgroup.map_subtype_le _
  refine Or.inr ⟨rfl, ?_, hR2, ?_, ?_⟩
  · refine h63 G M Q H E h hH2 hp hL ?_ ?_
    · rw [hK]
      exact hJ.1
    · rw [hK]
      rcases hJr with h1 | ⟨h2', hdvd⟩
      · exact Or.inl h1
      · refine Or.inr ⟨h2', ?_⟩
        intro hbot
        have h1 : Nat.card (center ↥J) = 1 := by rw [hbot, Subgroup.card_bot]
        have h31 : 3 ∣ 1 := by rwa [h1] at hdvd
        norm_num at h31
  · intro hxM
    exact hY (by
      have hmono := (h.le_iff_starImg_le hxH).mp hxM
      rwa [hXs] at hmono)
  · exact isPSolvable_d1PlusCore Nat.prime_three H (kStar 3 M H)
      (by rw [hK, ← hlay]; exact isSolvable_centralizer_layer_three H hR2.le)

end Certified

end NineSettingGen

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
