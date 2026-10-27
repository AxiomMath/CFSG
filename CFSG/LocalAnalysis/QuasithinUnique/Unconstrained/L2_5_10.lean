module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.Setting

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin

theorem lemma2510 : Lemma2510 := by
  intro G _ _ T M hs N
  refine ⟨fun U HU hpair => (hpair.1.1.charTwo_normalizer_core hs.setting hpair.1.2.1
    hpair.1.2.2.2.1).2, ?_⟩
  intro U HU hstar
  obtain ⟨hpair, hmaxU⟩ := hstar
  have hUHU : U ≤ HU := hpair.1.2.1
  have hHUH : HU ≤ N.H := hpair.2
  have hU2 : IsPGroup 2 U := hpair.1.1.2.2.1
  have hQ2 : IsPGroup 2 (pCoreOf 2 HU) :=
    CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 HU
  have hHUN : HU ≤ Subgroup.normalizer (pCoreOf 2 HU : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 HU
  have hcharN : CharTwo (Subgroup.normalizer (pCoreOf 2 HU : Set G)) :=
    (hpair.1.1.charTwo_normalizer_core hs.setting hUHU hpair.1.2.2.2.1).2
  set Nn := Subgroup.normalizer (pCoreOf 2 HU : Set G) with hNn
  have hUN : U ≤ Nn := hUHU.trans hHUN
  have hcoreN : pCoreOf 2 Nn ≠ ⊥ := by
    intro hbot
    have hle : pCoreOf 2 HU ≤ pCoreOf 2 Nn :=
      CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 _ Nn Subgroup.le_normalizer
        ((Subgroup.normal_subgroupOf_iff_le_normalizer Subgroup.le_normalizer).mpr le_rfl) hQ2
    rw [hbot] at hle
    exact hpair.1.2.2.1 (le_bot_iff.mp hle)
  obtain ⟨U₁, hUU₁, hU₁⟩ := exists_isSylowTwoOf_of_le hUN hU2
  have hconf₁ : IsConfining M U₁ := hpair.1.1.of_le hU₁.isPGroup hUU₁
  have hwit : IsWitnessPair M U₁ Nn :=
    ⟨hconf₁, hU₁.le, hcoreN, hcharN, fun hNM => hpair.1.2.2.2.2 (hHUN.trans hNM)⟩
  have hcard : Nat.card U₁ ≤ Nat.card U := hmaxU U₁ hwit.isWitness
  have hU₁U : U₁ = U :=
    (Subgroup.eq_of_le_of_card_ge hUU₁ hcard).symm
  have hUsylN : IsSylowTwoOf U Nn := hU₁U ▸ hU₁
  have hUsyl : IsSylowTwoOf U HU := by
    refine isSylowTwoOf_of_card_eq hUHU hU2 (le_antisymm (card_le_twoPart hUHU hU2) ?_)
    rw [hUsylN.card_eq]
    exact twoPart_mono hHUN
  refine ⟨hUsylN, hUsyl, fun hUS => ?_⟩
  have hzT : N.z ∈ centerOf T := N.tuple.z_mem
  have hST : N.S ≤ T := N.tuple.lt.le
  have hzS : N.z ∈ N.S := N.tuple.center_le hzT
  have hzc : N.z ∈ Subgroup.centralizer (N.S : Set G) :=
    Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hST) hzT.2
  have hO2U : pCoreOf 2 Nn ≤ U :=
    hUsylN.le_of_normalizes (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 Nn)
      (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 Nn)
      (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 Nn)
  have hQO : pCoreOf 2 HU ≤ pCoreOf 2 Nn :=
    CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 _ Nn Subgroup.le_normalizer
      ((Subgroup.normal_subgroupOf_iff_le_normalizer Subgroup.le_normalizer).mpr le_rfl) hQ2
  have hZU : centerOf N.S ≤ centerOf U := by
    intro w hw
    have hwS : w ∈ N.S := hw.1
    have hwcU : w ∈ Subgroup.centralizer (U : Set G) :=
      Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hUS) hw.2
    have hwcQ : w ∈ Subgroup.centralizer (pCoreOf 2 Nn : Set G) :=
      Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hO2U) hwcU
    have hwcQ' : w ∈ Subgroup.centralizer (pCoreOf 2 HU : Set G) :=
      Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hQO) hwcQ
    have hwN : w ∈ Nn := Subgroup.centralizer_le_normalizer _ hwcQ'
    exact ⟨hO2U (hcharN ⟨hwN, hwcQ⟩), hwcU⟩
  exact ⟨⟨hzS, hzc⟩, hZU⟩

end CFSG.QuasithinUnique
