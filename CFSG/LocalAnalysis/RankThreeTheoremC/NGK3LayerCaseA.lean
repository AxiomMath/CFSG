module

public import CFSG.LocalAnalysis.RankThreeTheoremC.NGK3Defs
import CFSG.LocalAnalysis.ComponentClassification.Layer
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.PerfectResiduals
import CFSG.LocalAnalysis.RankThreeTheoremC.NormalPlane

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {X : Type} [Group X] [Finite X] {P : Sylow 3 X} {z : X} {D : Subgroup X}

private theorem isMulCommutative_layerCenter : IsMulCommutative (layerCenter X) := by
  unfold layerCenter
  infer_instance

private theorem normal_layerCenter : (layerCenter X).Normal := by
  have hEn : (rankThreeLayer (⊤ : Subgroup X)).Normal :=
    CFSG.ComponentClassification.Layer.normal X
  rw [← normalizer_eq_top_iff, eq_top_iff]
  have hle := normalizer_le_normalizer_characteristic_map (rankThreeLayer (⊤ : Subgroup X))
    (center (rankThreeLayer (⊤ : Subgroup X))) inferInstance
  rwa [normalizer_eq_top (H := rankThreeLayer (⊤ : Subgroup X))] at hle

private theorem mem_layerCenter_of_mem_center {g : X}
    (hgE : g ∈ rankThreeLayer (⊤ : Subgroup X)) (hg : g ∈ center X) : g ∈ layerCenter X := by
  unfold layerCenter
  refine Subgroup.mem_map.2 ⟨⟨g, hgE⟩, ?_, rfl⟩
  rw [mem_center_iff]
  intro y
  exact Subtype.ext (mem_center_iff.1 hg y)

private theorem two_le_of_card_eq_pow {W : Subgroup X} {k : ℕ} (hk : Nat.card W = 3 ^ k)
    (hzW : z ∈ W) (hzo : orderOf z = 3) {w : X} (hwW : w ∈ W) (hwz : w ∉ zpowers z) :
    2 ≤ k := by
  by_contra hlt
  have hle : Nat.card W ≤ Nat.card (zpowers z) := by
    rw [hk, Nat.card_zpowers, hzo]
    calc 3 ^ k ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 3 := by norm_num
  exact hwz (Subgroup.eq_of_le_of_card_ge (zpowers_le.2 hzW) hle ▸ hwW)

theorem NGKData.caseA (h : NGKData X P z D) {w : X} (hw : w ∈ layerCenter X) (hw3 : w ^ 3 = 1)
    (hwz : w ∉ zpowers z) : ⊤ ≤ rankThreeAschCore 2 3 (P : Subgroup X) := by
  have hp3 : (3 : ℕ).Prime := Nat.prime_three
  have hz3 : z ^ 3 = 1 := h.ord ▸ pow_orderOf_eq_one z
  have hzZ : z ∈ layerCenter X := mem_layerCenter_of_mem_center h.layer h.zc
  have hWe : IsElemAbelian 3 (omegaOneOf 3 (layerCenter X)) :=
    isElemAbelian_omegaOneOf isMulCommutative_layerCenter
  have : (layerCenter X).Normal := normal_layerCenter
  have hWn : normalizer (omegaOneOf 3 (layerCenter X) : Set X) = ⊤ :=
    top_le_iff.1 (by
      rw [← normalizer_eq_top (H := layerCenter X)]
      exact normalizer_le_normalizer_omegaOneOf 3 (layerCenter X))
  have : (omegaOneOf 3 (layerCenter X)).Normal := normalizer_eq_top_iff.1 hWn
  have hzW : z ∈ omegaOneOf 3 (layerCenter X) := subset_closure ⟨hzZ, hz3⟩
  have hwW : w ∈ omegaOneOf 3 (layerCenter X) := subset_closure ⟨hw, hw3⟩
  have hWP : omegaOneOf 3 (layerCenter X) ≤ (P : Subgroup X) :=
    (elementary_isPGroup 3 _ hWe).le_sylow_of_normal P
  have := Fact.mk hp3
  obtain ⟨k, hk⟩ := (elementary_isPGroup 3 _ hWe).exists_card_eq
  have hkle : k ≤ CFSG.Open.pRank 3 (omegaOneOf 3 (layerCenter X)) :=
    le_csSup (pRank_set_bddAbove 3 hp3.one_lt _) ⟨_, le_rfl, hWe, hk⟩
  have hk2 : 2 ≤ k := two_le_of_card_eq_pow hk hzW h.ord hwW hwz
  have hgood : 3 ≤ CFSG.Open.pRank 3
      (omegaOneOf 3 (layerCenter X) ⊔ ((P : Subgroup X) ⊓
        centralizer (omegaOneOf 3 (layerCenter X) : Set X))) := by
    rcases Nat.lt_or_ge k 3 with hk3 | hk3
    · have hk2' : k = 2 := by omega
      exact three_le_pRank_sup_centralizer_of_normal_elemAbelian hp3 h.prank.ge
        (hWn ▸ le_top) hWe (hk2' ▸ hk)
    · exact (hk3.trans hkle).trans (pRank_mono 3 hp3.one_lt le_sup_left)
  rw [← hWn]
  exact aschCore_normalizer_le 2 3 (P : Subgroup X) _ hWP (hk2.trans hkle) hgood

end CFSG.LocalAnalysis.RankThreeTheoremC
