module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CHHMinimal
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CHHPower
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CHHOrbit
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CHHRank

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open Subgroup
open scoped commutatorElement

theorem HHMinimal.three_le_pRank {K : Type*} [Group K] [Finite K] {B Q : Subgroup K} {d : ℕ}
    (h : HHMinimal B Q) (hd : d.Prime) (hd5 : 5 ≤ d) (hQ : IsPGroup 3 Q) (hB : IsPGroup d B) :
    3 ≤ CFSG.Open.pRank 3 Q := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hd3 : d ≠ 3 := by omega
  have hcomm : ⁅Q, B⁆ = Q := h.commutator_eq hd hd3 hQ hB
  have hQ'B : ⁅Q, Q⁆ ≤ centralizer (B : Set K) := h.commutator_self_le_centralizer hQ
  have hclass : ⁅Q, Q⁆ ≤ centralizer (Q : Set K) :=
    h.commutator_self_le_centralizer_self hd hd3 hQ hB
  have hFZ : Q ⊓ centralizer (B : Set K) ≤ centralizer (Q : Set K) :=
    inf_centralizer_le_centralizer_self h.normalizes hcomm hclass hQ'B
  have hcubeB : ∀ x ∈ Q, x ^ 3 ∈ centralizer (B : Set K) := h.pow_three_mem_centralizer hQ
  have hcubeZ : ∀ x ∈ Q, x ^ 3 ∈ centralizer (Q : Set K) := fun x hx =>
    hFZ (Subgroup.mem_inf.mpr ⟨Q.pow_mem hx 3, hcubeB x hx⟩)
  have hexp : ∀ x ∈ Q, x ^ 3 = 1 :=
    pow_three_eq_one h.normalizes hcomm hclass hcubeB hcubeZ
  have hnot : ¬ Q ≤ centralizer (B : Set K) := fun hle =>
    h.nontrivial (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hle)
  have h27 : 3 ^ 3 ≤ (centralizer (B : Set K)).relIndex Q :=
    three_pow_three_le_relIndex_centralizer hd hd5 hQ hB h.normalizes hnot
  by_cases hab : ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x
  ·
    have hE : CFSG.Open.IsElemAbelian 3 Q :=
      ⟨⟨⟨fun a b => Subtype.ext (hab a a.2 b b.2)⟩⟩, hexp⟩
    obtain ⟨k, hk⟩ := hQ.exists_card_eq
    have hle : 3 ^ 3 ≤ 3 ^ k :=
      h27.trans (hk ▸ Nat.le_of_dvd Nat.card_pos (Subgroup.relIndex_dvd_card _ _))
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 hle |>.trans
      (CFSG.SectionRank.le_pRank (by norm_num) le_rfl hE hk)
  ·
    have hZB : Q ⊓ centralizer (Q : Set K) ≤ centralizer (B : Set K) :=
      h.inf_centralizer_le_of_not_comm hab
    have hsub : (centralizer (B : Set K)).subgroupOf Q =
        (centralizer (Q : Set K)).subgroupOf Q := by
      ext x
      simp only [Subgroup.mem_subgroupOf]
      exact ⟨fun hx => hFZ (Subgroup.mem_inf.mpr ⟨x.2, hx⟩),
        fun hx => hZB (Subgroup.mem_inf.mpr ⟨x.2, hx⟩)⟩
    have h27' : 3 ^ 3 ≤ (centralizer (Q : Set K)).relIndex Q := by
      unfold Subgroup.relIndex at h27 ⊢
      rwa [hsub] at h27
    exact three_le_pRank_of_exponent_three hexp hclass h27'

theorem le_centralizer_of_pRank_le_two {K : Type*} [Group K] [Finite K] {A W : Subgroup K}
    {d : ℕ} (hd : d.Prime) (hd5 : 5 ≤ d) (hA : IsPGroup 3 A)
    (hrk : CFSG.Open.pRank 3 A ≤ 2) (hW : IsPGroup d W)
    (hWA : W ≤ normalizer (A : Set K)) : W ≤ centralizer (A : Set K) := by
  by_contra hne
  have hcomm : ⁅A, W⁆ ≠ ⊥ := fun h => hne (by
    rw [Subgroup.commutator_comm] at h
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h)
  obtain ⟨Q, hQA, hmin⟩ := exists_hhMinimal hWA hcomm
  have h3 := hmin.three_le_pRank hd hd5 (hA.to_le hQA) hW
  have hmono := CFSG.SectionRank.pRank_mono (by norm_num : 1 < 3) hQA
  omega

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
