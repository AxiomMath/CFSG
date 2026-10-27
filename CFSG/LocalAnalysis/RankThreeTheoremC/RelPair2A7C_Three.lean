module

public import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2A7C_Defs
import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2A7B_Cover
public import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2_Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup Equiv
  CFSG.RankThree.PartTwo.KFacts.KP2

variable {G : Type} [Group G] [Finite G]

theorem a7w_exists_lift {D H V : Subgroup G} {ι : ↥H →* Perm (Fin 7)}
    (hF : A7Frame D H V ι) {J : Subgroup G}
    (hJι : (J.subgroupOf H).map ι = alternatingGroup (Fin 7)) (hDJ : D ≤ J)
    {W : Subgroup (Perm (Fin 7))} (hW2 : IsPGroup 2 W) (hWA : W ≤ alternatingGroup (Fin 7))
    (hWE : eNine ≤ normalizer (W : Set (Perm (Fin 7)))) :
    ∃ B : Subgroup ↥H, B ≤ J.subgroupOf H ∧ IsPGroup 2 B ∧
      D.subgroupOf H ≤ normalizer (B : Set ↥H) ∧ B.map ι = W := by
  have hWr : W ≤ ι.range := hWA.trans hF.A7_le
  have hker : (3 : ℕ).Coprime (Nat.card ι.rangeRestrict.ker) := by
    rw [MonoidHom.ker_rangeRestrict, hF.ker_eq]
    exact primeComplementCore_coprime 3
  have hD3 : IsPGroup 3 (D.subgroupOf H) :=
    hF.D_three.of_equiv (Subgroup.subgroupOfEquivOfLe hF.D_le).symm
  have hW2' : IsPGroup 2 (W.subgroupOf ι.range) :=
    hW2.of_equiv (Subgroup.subgroupOfEquivOfLe hWr).symm
  have hDJ' : D.subgroupOf H ≤ J.subgroupOf H := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (hDJ (Subgroup.mem_subgroupOf.mp hx))
  have hQW : (D.subgroupOf H).map ι.rangeRestrict ≤
      normalizer ((W.subgroupOf ι.range : Subgroup ↥ι.range) : Set ↥ι.range) := by
    rw [← Subgroup.subgroupOf_normalizer_eq hWr]
    rintro _ ⟨d, hd, rfl⟩
    rw [Subgroup.mem_subgroupOf, MonoidHom.coe_rangeRestrict]
    have hdE : ι d ∈ eNine := by
      rw [← hF.D_img]
      exact Subgroup.mem_map_of_mem ι hd
    exact hWE hdE
  have hWN : W.subgroupOf ι.range ≤ (J.subgroupOf H).map ι.rangeRestrict := by
    intro w hw
    have hw' : (w : Perm (Fin 7)) ∈ (J.subgroupOf H).map ι := by
      rw [hJι]
      exact hWA (Subgroup.mem_subgroupOf.mp hw)
    obtain ⟨j, hj, hjw⟩ := hw'
    exact ⟨j, hj, Subtype.ext hjw⟩
  obtain ⟨B, hBN, hB2, hDB, hBW⟩ := exists_invariantTwo_lift Nat.prime_three (by norm_num)
    ι.rangeRestrict (MonoidHom.rangeRestrict_surjective ι) hker hDJ' hD3 hW2' hQW hWN
  refine ⟨B, hBN, hB2, hDB, ?_⟩
  rw [← MonoidHom.subtype_comp_rangeRestrict ι, ← Subgroup.map_map, hBW,
    Subgroup.map_subgroupOf_eq_of_le hWr]

theorem A7Frame.exists_J_three {D H V : Subgroup G} {ι : ↥H →* Perm (Fin 7)}
    (hF : A7Frame D H V ι) {J : Subgroup G} (hJH : J ≤ H)
    (hJι : (J.subgroupOf H).map ι = alternatingGroup (Fin 7)) (hDJ : D ≤ J) :
    3 ∣ Nat.card (invariantTwoJoinIn D J) := by
  have h4 : (4 : ℕ) = 2 ^ 2 := by norm_num
  obtain ⟨B₁, hB₁J, hB₁2, hDB₁, hB₁ι⟩ := a7w_exists_lift hF hJι hDJ
    (IsPGroup.of_card (card_vOne.trans h4)) vOne_le_alternatingGroup eNine_le_normalizer_vOne
  obtain ⟨B₂, hB₂J, hB₂2, hDB₂, hB₂ι⟩ := a7w_exists_lift hF hJι hDJ
    (IsPGroup.of_card (card_vTwo.trans h4)) vTwo_le_alternatingGroup eNine_le_normalizer_vTwo
  have hle : ∀ B : Subgroup ↥H, B ≤ J.subgroupOf H → IsPGroup 2 B →
      D.subgroupOf H ≤ normalizer (B : Set ↥H) → B.map H.subtype ≤ invariantTwoJoinIn D J := by
    intro B hBJ hB2 hDB
    refine le_invariantTwoJoinIn ?_ (hB2.map _) ?_
    · exact (Subgroup.map_mono hBJ).trans (Subgroup.map_subgroupOf_eq_of_le hJH).le
    · intro d hd
      have hdy : (⟨d, hF.D_le hd⟩ : ↥H) ∈ D.subgroupOf H := Subgroup.mem_subgroupOf.mpr hd
      exact Subgroup.le_normalizer_map H.subtype ⟨_, hDB hdy, rfl⟩
  have hsup : (B₁ ⊔ B₂).map H.subtype ≤ invariantTwoJoinIn D J := by
    rw [Subgroup.map_sup]
    exact sup_le (hle B₁ hB₁J hB₁2 hDB₁) (hle B₂ hB₂J hB₂2 hDB₂)
  have h3 : 3 ∣ Nat.card (B₁ ⊔ B₂ : Subgroup ↥H) := by
    have h := Subgroup.card_map_dvd (B₁ ⊔ B₂) ι
    rw [Subgroup.map_sup, hB₁ι, hB₂ι] at h
    exact three_dvd_card_vOne_sup_vTwo.trans h
  rw [← Subgroup.card_map_of_injective H.subtype_injective (K := B₁ ⊔ B₂)] at h3
  exact h3.trans (Subgroup.card_dvd_of_le hsup)

end CFSG.LocalAnalysis.RankThreeTheoremC
