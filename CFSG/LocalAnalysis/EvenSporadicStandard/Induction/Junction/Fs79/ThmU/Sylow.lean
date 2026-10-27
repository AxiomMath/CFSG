module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.Fs79.ThmU.Criteria
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.Fs79.ThmU.SwapPair
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.Fs79.ThmU.Rank

public section

namespace CFSG.EvenSporadicStandard.Induction.ThmU

open Subgroup CFSG.EvenSporadicStandard.Solomon78 CFSG.EvenSporadicStandard.Induction
  CFSG.ComponentClassification.AschbacherToolkit
open scoped commutatorElement

variable {G : Type} [Group G]

theorem no_bad_in_sylow [Finite G] (hLB : LayerBalanceAt G) (hglaub : GlaubermanSimplePerfect)
    {B : Subgroup G} (hB : MaximalF B) {u₁ u₂ : G} (h₁ : GoodInv B u₁) (h₂ : GoodInv B u₂)
    (h₃ : GoodInv B (u₁ * u₂)) (h12 : u₁ * u₂ = u₂ * u₁) {T : Subgroup G} (hT : IsPGroup 2 T)
    (hTB : T ≤ centralizer (B : Set G)) (hu₁ : u₁ ∈ T) (hu₂ : u₂ ∈ T)
    (hrank : 3 ≤ CFSG.Open.pRank 2 T) : ¬ ∃ y ∈ T, BadInv B y := by
  rintro ⟨y, hyT, hy⟩
  obtain ⟨y, hyT, hy, hmax⟩ := exists_max_bad ⟨y, hyT, hy⟩
  let P : Subgroup G := T ⊓ centralizer ({y} : Set G)
  have hBc : ∀ t ∈ T, ∀ b ∈ B, t * b = b * t := by
    intro t ht b hb
    exact (Subgroup.mem_centralizer_iff.1 (hTB ht) b hb).symm
  obtain ⟨z, hzT, hz2, hzc⟩ := exists_central_involution hT hu₁ h₁.1
  have hzB : B ≤ centralizer ({z} : Set G) := by
    intro b hb
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.1 (hTB hzT) b hb
  have hzgood : GoodInv B z :=
    goodInv_of_fourGroup hLB hglaub hB h₁ h₂ h₃ h12 hz2 hzB (hzc u₁ hu₁).symm (hzc u₂ hu₂).symm
  have hne : ∃ t ∈ T, y * t ≠ t * y := by
    by_contra hcon
    push Not at hcon
    exact hy.not_goodInv
      (goodInv_of_fourGroup hLB hglaub hB h₁ h₂ h₃ h12 hy.1 hy.2.1
        (hcon u₁ hu₁).symm (hcon u₂ hu₂).symm)
  have hyz : y ≠ z := by
    rintro rfl
    exact hy.not_goodInv hzgood
  have hyz_comm : y * z = z * y := (hzc y hyT).symm
  have hyP : y ∈ P :=
    ⟨hyT, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩
  have hzP : z ∈ P :=
    ⟨hzT, Subgroup.mem_centralizer_singleton_iff.2 (hzc y hyT)⟩
  have h4 : 4 ≤ Nat.card P :=
    four_le_card_of_involutions hy.1 hz2 hyz hyz_comm hyP hzP
  have hne4 : Nat.card P ≠ 4 := by
    intro h4eq
    have hle : CFSG.Open.pRank 2 T ≤ 2 :=
      pRank_le_two_of_centralizer_card_four' hT hyT hy.1 h4eq
    omega
  have hP2 : IsPGroup 2 P := hT.to_le inf_le_left
  have h8 : 8 ≤ Nat.card P := eight_le_card hP2 h4 hne4
  obtain ⟨g, hgT, -, hy'P, hy'cent, hw2, hlt⟩ := exists_conj_in_center hT hyT hy.1 hne
  have hy'bad : BadInv B (g * y * g⁻¹) :=
    hy.conj (c := g) fun b hb => hBc g hgT b hb
  have hy'T : g * y * g⁻¹ ∈ T := hy'P.1
  have hwT : y * (g * y * g⁻¹) ∈ T := T.mul_mem hyT hy'T
  have hBw : B ≤ centralizer ({y * (g * y * g⁻¹)} : Set G) := by
    intro b hb
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.1 (hTB hwT) b hb
  have hwgood : GoodInv B (y * (g * y * g⁻¹)) :=
    goodInv_of_not_badInv hw2 hBw fun hbadw =>
      (not_lt_of_ge (hmax (y * (g * y * g⁻¹)) hwT hbadw)) hlt
  exact false_of_commuting_bad_pair hLB hglaub hB hzgood hy hy'bad hwgood hP2 h8
    (fun p hp b hb => hBc p hp.1 b hb)
    hzP (fun p hp => (hzc p hp.1).symm)
    hyP hy'P (fun p hp => Subgroup.mem_centralizer_singleton_iff.1 hp.2)
    (fun p hp => hy'cent p hp)

theorem universalF_of_fourGroup [Finite G] (hLB : LayerBalanceAt G)
    (hglaub : GlaubermanSimplePerfect) {B : Subgroup G} (hB : MaximalF B) {u₁ u₂ : G}
    (h₁ : GoodInv B u₁) (h₂ : GoodInv B u₂) (h₃ : GoodInv B (u₁ * u₂))
    (h12 : u₁ * u₂ = u₂ * u₁) (h3 : 3 ≤ CFSG.Open.pRank 2 (centralizer (B : Set G))) :
    UniversalF B := by
  classical
  by_contra hnu
  rw [UniversalF] at hnu
  push Not at hnu
  obtain ⟨y₀, hy₀⟩ := hnu
  let C : Subgroup G := centralizer (B : Set G)
  have hu₁C : u₁ ∈ C := by
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact Subgroup.mem_centralizer_singleton_iff.1 (h₁.le_centralizer hb)
  have hu₂C : u₂ ∈ C := by
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact Subgroup.mem_centralizer_singleton_iff.1 (h₂.le_centralizer hb)
  have hUC : zpowers u₁ ⊔ zpowers u₂ ≤ C :=
    sup_le (Subgroup.zpowers_le.2 hu₁C) (Subgroup.zpowers_le.2 hu₂C)
  have hU : IsPGroup 2 ↥(zpowers u₁ ⊔ zpowers u₂) :=
    isPGroup_two_sup_zpowers h₁.1 h₂.1 h12
  obtain ⟨T, hTC, hT, hUT, hconj⟩ := exists_sylow_forall_conj hU hUC
  have hy₀C : y₀ ∈ C := by
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact Subgroup.mem_centralizer_singleton_iff.1 (hy₀.2.1 hb)
  have hy₀U : IsPGroup 2 ↥(zpowers y₀) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hy₀.1]; norm_num)
  obtain ⟨c, hcC, hcj⟩ := hconj (zpowers y₀) hy₀U (Subgroup.zpowers_le.2 hy₀C)
  have hyT : c * y₀ * c⁻¹ ∈ T := hcj (conj_mem_cj (Subgroup.mem_zpowers y₀))
  have hybad : BadInv B (c * y₀ * c⁻¹) :=
    hy₀.conj (c := c) fun b hb => (Subgroup.mem_centralizer_iff.1 hcC b hb).symm
  have hrank : 3 ≤ CFSG.Open.pRank 2 T := three_le_pRank_of_conj hconj h3
  exact no_bad_in_sylow hLB hglaub hB h₁ h₂ h₃ h12 hT hTC
    (hUT (Subgroup.mem_sup_left (Subgroup.mem_zpowers u₁)))
    (hUT (Subgroup.mem_sup_right (Subgroup.mem_zpowers u₂)))
    hrank ⟨c * y₀ * c⁻¹, hyT, hybad⟩

end CFSG.EvenSporadicStandard.Induction.ThmU
