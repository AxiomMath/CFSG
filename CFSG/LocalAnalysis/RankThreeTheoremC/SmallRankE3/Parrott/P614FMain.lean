module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614Defs
import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614FKS
import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2Z_ApplyAux1

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614F

theorem pieceChevAlt_holds : PieceChevAlt := by
  intro hZJ G _ _ P M x z H S K hyp _ hvi hK
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : IsSimpleGroup G := hyp.setting.simple
  have hopt := hyp.optimal
  have hSH : S ≤ H := hopt.maxInv.1.1
  have hS2 : IsPGroup 2 S := hopt.maxInv.1.2.1
  have hSM : S ≤ M := hopt.ext.pair.isMax.1.1.trans inf_le_right
  have hD2 : IsPGroup 2 (rankThreePrimeCore 3 H) := by
    rw [hvi]
    exact isPGroup_pCoreOf 2 H
  have hHtop : H ≠ ⊤ := CFSG.RankThreeCoreUniqueness.Helpers.twoLocal_ne_top
    hyp.setting.nonab H hopt.ext.pair.isTwoLocal
  obtain ⟨X, hX⟩ : ∃ X : Subgroup G, K ⊔ S = X := ⟨_, rfl⟩
  have hKX : K ≤ X := hX ▸ le_sup_left
  have hSX : S ≤ X := hX ▸ le_sup_right
  have hXH : X ≤ H := hX ▸ sup_le hK.le hSH
  have hXK : X ≤ normalizer (K : Set G) := hXH.trans hK.normal
  haveI hKn : (K.subgroupOf X).Normal := (normal_subgroupOf_iff_le_normalizer hKX).mpr hXK
  have hS2' : IsPGroup 2 (S.subgroupOf X) := hS2.comap_subtype
  have hKS : K.subgroupOf X ⊔ S.subgroupOf X = ⊤ := by
    apply Subgroup.map_injective X.subtype_injective
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hKX,
      Subgroup.map_subgroupOf_eq_of_le hSX, hX, Subgroup.map_top, Subgroup.range_subtype]
  have hN2 := isPGroup_pPrimeCore hK hD2 hKX hSX hX hS2 hXK
  have hcoreS := pCore_le_subgroupOf hK hX hopt.ext.pair.le hopt.maxInv
  have hNS : CFSG.pPrimeCore 3 ↥X ≤ S.subgroupOf X :=
    (le_sSup ⟨inferInstance, hN2⟩ : CFSG.pPrimeCore 3 ↥X ≤ CFSG.pCore 2 ↥X).trans hcoreS
  have hcoreM : (CFSG.pPrimeCore 3 ↥X).map X.subtype ≤ M := by
    rintro _ ⟨g, hg, rfl⟩
    exact hSM (Subgroup.mem_subgroupOf.mp (hNS hg))
  have h3 : ¬ 3 ∣ Nat.card (⁅K.subgroupOf X,
      (CFSG.pPrimeCore 3 ↥(K.subgroupOf X)).map (K.subgroupOf X).subtype⁆ : Subgroup ↥X) := by
    intro hdvd
    have hle := Subgroup.card_dvd_of_le (Subgroup.commutator_le_right (K.subgroupOf X)
      ((CFSG.pPrimeCore 3 ↥(K.subgroupOf X)).map (K.subgroupOf X).subtype))
    rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _)] at hle
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp CFSG.pPrimeCore_coprime_card
      (hdvd.trans hle)
  have hT : ∃ T : Sylow 2 ↥X, K.subgroupOf X ⊔ (T : Subgroup ↥X) = ⊤ := by
    obtain ⟨T, hT⟩ := hS2'.exists_le_sylow
    exact ⟨T, eq_top_iff.mpr (hKS.ge.trans (sup_le_sup_left hT _))⟩
  have h2cl : ∀ T₂ : Sylow 2 (CFSG.pPrimeCore 3 ↥X),
      (T₂ : Subgroup (CFSG.pPrimeCore 3 ↥X)).Normal := by
    intro T₂
    rw [← T₂.is_maximal' (hN2.to_subgroup ⊤) le_top]
    infer_instance
  have key := hZJ 3 Nat.prime_three (by norm_num) ↥X
    (CFSG.AGLEmbedding.catalogSimpleSections_of_isKProper hyp.setting.kProper X
      (ne_top_of_le_ne_top hHtop hXH))
    (centralizer_pCore_le_of_le hXH (hopt.core_le.trans hSX)
      (hyp.setting.charTwo H hopt.ext.pair.isTwoLocal))
    (K.subgroupOf X) hKn (isPComponent_subgroupOf hK hD2 hKX hXK) hT h3 h2cl
    (S.subgroupOf X) hS2' hcoreS (not_le_normalizer_sup hK hKX hSX hopt.char_le hcoreM)
  obtain ⟨e⟩ := nonempty_quotient_center_equiv hK hKX
  exact zja_chevTwo_or_alt_of_mulEquiv e key

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614
