module

public import CFSG.LocalAnalysis.RankFourTheoremC.RelativePair.JZero
public import CFSG.LocalAnalysis.RankFourTheoremC.RelativePair.ThreeRank
public import CFSG.LocalAnalysis.RankFourTheoremC.RelativePair.Thompson
public import CFSG.LocalAnalysis.RankFourTheoremC.RelativePair.ZJ
import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2T_Plumb
import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2Z_Exp
import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2Z_Rank
public import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2Z_Plumb

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools
  CFSG.LocalAnalysis.RankThreeTheoremC Subgroup

variable {G : Type} [Group G] [Finite G]

theorem ObstructionSetting.not_dvd_card_invariantTwoJoinIn_of_faithful (hS : ObstructionSetting G)
    (hD1 : TheoremD1 G) {p : ℕ} (hp : p ∈ rankThreeSigmaA G) (hR : TransitivityReduction G)
    (h13 : GL83InvariantTwoSylow G) {P : Sylow p G} {M D R T H V : Subgroup G}
    (hd : MaximalRelativePair p P M D R T) (hopt : IsOptimalRelPair p M D R T H V)
    (hp5 : 5 ≤ p) {Q : Subgroup ↥H} (hQ3 : IsPGroup 3 Q)
    (hDQ : D.subgroupOf H ≤ normalizer (Q : Set ↥H))
    (hfaith : D.subgroupOf H ⊓ centralizer (Q : Set ↥H) = ⊥) :
    ¬ p ∣ Nat.card (invariantTwoJoinIn (D.subgroupOf H) (normalizer (Q : Set ↥H))) := by
  have hprime := sigmaA_prime p hp
  obtain ⟨hDe, hDc⟩ := hd.ext.isElemAbelian_of_isMulCommutative hprime hd.abelian
  have hDH : D ≤ H := (le_sup_right : D ≤ relPairBase R T ⊔ D).trans hopt.pair.cand.base_le
  set Q' : Subgroup G := Q.map H.subtype with hQ'
  have hQ'H : Q' ≤ H := Subgroup.map_subtype_le Q
  have hQ'3 : IsPGroup 3 Q' := hQ3.map H.subtype
  have hDQ' : D ≤ normalizer (Q' : Set G) := fun g hg =>
    thg_mem_normalizer_map (hDQ (show (⟨g, hDH hg⟩ : H) ∈ D.subgroupOf H from hg))
  have hfaith' : D ⊓ centralizer (Q' : Set G) = ⊥ := by
    rw [eq_bot_iff]
    intro d hd
    obtain ⟨hdD, hdC⟩ := Subgroup.mem_inf.mp hd
    rw [Subgroup.mem_bot]
    have hmem : (⟨d, hDH hdD⟩ : H) ∈ D.subgroupOf H ⊓ centralizer (Q : Set ↥H) := by
      refine Subgroup.mem_inf.mpr ⟨hdD, Subgroup.mem_centralizer_iff.mpr fun q hq => ?_⟩
      exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp hdC) (q : G) ⟨q, hq, rfl⟩)
    rw [hfaith, Subgroup.mem_bot] at hmem
    exact congrArg Subtype.val hmem
  have hAex := exists_isElemAbelian_card_three_pow_four hprime hp5 hDe hDc hQ'3 hDQ' hfaith'
  have hBex := exists_isElemAbelian_card_three_pow_three_of_faithful hprime hp5 hDe hDc hQ'3 hDQ'
    hfaith'
  have hG := hS.not_dvd_card_invariantTwoJoinIn_of_rank_three hD1 hp hd.ext hd.not_le_normalizer hR
    h13 hopt.pair.cand.twoLocal hQ'H hQ'3 hAex hBex
  intro hdvd
  apply hG
  have hle := zjp_join_le hDH Q
  have h1 : p ∣ Nat.card ((invariantTwoJoinIn (D.subgroupOf H)
      (normalizer (Q : Set ↥H))).map H.subtype) := by
    rwa [Subgroup.card_map_of_injective H.subtype_injective]
  exact h1.trans (Subgroup.card_dvd_of_le hle)

theorem KFactSetting.zjFrameGe {n : ℕ} {p : ℕ} {P : Sylow p G} {M D R T H V : Subgroup G}
    (hS : KFactSetting n G) (hD1 : TheoremD1 G) (hR : TransitivityReduction G)
    (h13 : GL83InvariantTwoSylow G) (hp : p ∈ rankThreeSigmaA G)
    (hd : MaximalRelativePair p P M D R T) (hopt : IsOptimalRelPair p M D R T H V)
    (hfacts : OptimalRelPairFacts p M D H V) :
    ZJFrameGe p (primeComplementCore (G := H) p) (D.subgroupOf H) (V.subgroupOf H) := by
  have := hS.simple
  have hTwoLocal : IsTwoLocal H := hopt.pair.cand.twoLocal
  have hDH : D ≤ H := (le_sup_right : D ≤ relPairBase R T ⊔ D).trans hopt.pair.cand.base_le
  have hVH : V ≤ H := hfacts.maximal.1
  have hV2 : IsPGroup 2 V := hfacts.maximal.2.1
  have hDV : D ≤ normalizer (V : Set G) := hfacts.maximal.2.2.1
  refine
    { pre := hS.obstruction.thompsonPreFrame hD1 hR h13 hp hd hopt hfacts
      exists_component := ?_
      sections := CFSG.AGLEmbedding.catalogSimpleSections_of_isKProper hS.kProper H
        (twoLocal_ne_top hS.nonab H hTwoLocal)
      three := fun hp5 Q hQ3 hDQ hfaith =>
        hS.obstruction.not_dvd_card_invariantTwoJoinIn_of_faithful hD1 hp hR h13 hd hopt hp5 hQ3
          hDQ hfaith
      charTwo := ?_
      sylow2 := ?_
      V_two := hV2.of_equiv (Subgroup.subgroupOfEquivOfLe hVH).symm
      D_norm := ?_
      core_le := ?_
      noncover := ?_
      exp := (hS.obstruction.normalizerExponent hD1 hR h13 hp hd).subgroupOf hDH }
  · obtain ⟨L, hL, -, -, -, hpL, hcat⟩ := hfacts.exists_component
    exact ⟨L, (CFSG.isComponent_iff_open L).mpr hL, hpL, hcat⟩
  · intro c hc
    have hcH : (c : G) ∈ H ⊓ centralizer (pCoreOf 2 H : Set G) := by
      refine ⟨c.2, ?_⟩
      show (c : G) ∈ centralizer (pCoreOf 2 H : Set G)
      rw [mem_centralizer_iff]
      rintro _ ⟨y, hy, rfl⟩
      exact congrArg Subtype.val (mem_centralizer_iff.mp hc y hy)
    obtain ⟨y, hy, hyc⟩ := hS.obstruction.charTwo H hTwoLocal hcH
    have : y = c := Subtype.ext hyc
    rwa [← this]
  · rw [← isSylowOf_map_subtype_iff H]
    exact hfacts.sylow
  · rw [← Subgroup.subgroupOf_normalizer_eq hVH]
    exact fun x hx => Subgroup.mem_subgroupOf.mpr (hDV (Subgroup.mem_subgroupOf.mp hx))
  · intro x hx
    exact hfacts.pCore_le ⟨x, hx, rfl⟩
  · intro Z hZV hZ1 hZc hdvd
    have hZgV : Z.map H.subtype ≤ V := by
      rintro _ ⟨z, hz, rfl⟩
      exact hZV hz
    have hZg1 : Z.map H.subtype ≠ ⊥ := fun h => hZ1 (eq_bot_iff.mpr fun z hz => by
      have : (z : G) ∈ (⊥ : Subgroup G) := h ▸ ⟨z, hz, rfl⟩
      exact Subtype.ext (Subgroup.mem_bot.mp this))
    refine hfacts.not_dvd _ hZgV hZg1 (zjp_normalizer_le hVH hZV hZc) (hdvd.trans ?_)
    rw [← Subgroup.card_map_of_injective H.subtype_injective]
    exact Subgroup.card_dvd_of_le (zjp_join_le hDH Z)

theorem KFactSetting.gl83RelPair2ThompsonAlt_of_kfacts {n : ℕ} (hS : KFactSetting n G)
    (hD1 : TheoremD1 G) (hR : TransitivityReduction G) (h13 : GL83InvariantTwoSylow G)
    (hK1 : KFactZJFactorizationGe) (hK2 : KFactAlmostSimpleRankTwo) :
    GL83RelPair2ThompsonAlt G := by
  intro p hp P M D R T H V hd hopt hfacts
  obtain ⟨L, hL, hn⟩ := (hS.zjFrameGe hD1 hR h13 hp hd hopt hfacts).exists_alt hK1 hK2
  exact ⟨L, (CFSG.isComponent_iff_open L).mp hL, hn⟩

end CFSG.LocalAnalysis.RankFourTheoremC
