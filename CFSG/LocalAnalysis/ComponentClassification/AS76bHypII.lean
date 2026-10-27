module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bDefs
import CFSG.LocalAnalysis.ComponentClassification.TightEmbeddingConjugate

public section

namespace CFSG.ComponentClassification.AS76b

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding

variable {H : Type*} [Group H]

theorem inf_centralizer_eq_bot_of_not_le_gammaOneOn {T B : Subgroup H}
    (hΓ : ¬ B ≤ gammaOneOn T B) : T ⊓ centralizer (B : Set H) = ⊥ := by
  rw [eq_bot_iff]
  intro t ht
  rw [mem_bot]
  by_contra ht1
  apply hΓ
  intro b hb
  have hU : zpowers t ≤ T := (zpowers_le).2 ht.1
  have hU1 : zpowers t ≠ ⊥ := fun h => ht1 (zpowers_eq_bot.mp h)
  have hbt : Commute b t := (mem_centralizer_iff.mp ht.2 b hb)
  have hbc : b ∈ centralizer (zpowers t : Set H) := by
    rw [mem_centralizer_iff]
    intro x hx
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hx
    exact ((hbt.zpow_right n).symm).eq
  have hle : B ⊓ normalizer (zpowers t : Set H) ≤ gammaOneOn T B :=
    le_iSup₂_of_le (zpowers t) hU (le_iSup_of_le hU1 le_rfl)
  exact hle ⟨hb, centralizer_le_normalizer _ hbc⟩

theorem IsTwoNilpotent.mono [Finite H] {Q X : Subgroup H} (hQ : IsTwoNilpotent Q)
    (hXQ : X ≤ Q) : IsTwoNilpotent X := by
  obtain ⟨N, hNQ, hNn, hNodd, k, hk⟩ := hQ
  have hQN : Q ≤ normalizer (N : Set H) := (normal_subgroupOf_iff_le_normalizer hNQ).mp hNn
  refine ⟨N ⊓ X, inf_le_right, ?_, hNodd.of_dvd_nat (card_dvd_of_le inf_le_left), ?_⟩
  · refine (normal_subgroupOf_iff_le_normalizer inf_le_right).mpr fun x hx => ?_
    rw [mem_normalizer_iff]
    intro y
    have h1 := (mem_normalizer_iff.mp (hQN (hXQ hx))) y
    constructor
    · rintro ⟨hyN, hyX⟩
      exact ⟨h1.mp hyN, X.mul_mem (X.mul_mem hx hyX) (X.inv_mem hx)⟩
    · rintro ⟨hyN, hyX⟩
      refine ⟨h1.mpr hyN, ?_⟩
      have := X.mul_mem (X.mul_mem (X.inv_mem hx) hyX) hx
      simpa [mul_assoc] using this
  · have hN' : (N.subgroupOf Q).Normal := hNn
    rw [inf_relIndex_right, ← relIndex_subgroupOf hXQ]
    have hdvd : (N.subgroupOf Q).relIndex (X.subgroupOf Q) ∣ 2 ^ k := by
      rw [← relIndex_sup_left, ← hk]
      exact relIndex_dvd_index_of_le le_sup_left
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    exact ⟨m, hm⟩

theorem tightlyEmbedded_inf_subgroupOf {Q M M' : Subgroup H} (hMM' : M ≤ M')
    (htight : TightlyEmbedded (Q.subgroupOf M')) (heven : Even (Nat.card (Q ⊓ M : Subgroup H))) :
    TightlyEmbedded ((Q ⊓ M).subgroupOf M) :=
  StandardSubgroupAPI.tightlyEmbedded_inf_subgroupOf_of_le hMM' htight heven

theorem asc76HypII_of_hypII {A : Type*} [Group A] (hq : Open.IsQuasisimple A) (h : HypII A) :
    Asc76HypII A := by
  refine ⟨hq, fun H _ _ B Q T hiso hQN hTQ hΓ hel h4 hnil htight => ?_⟩
  have hTQle : T ≤ Q := hTQ.le
  have hTX : T ≤ Q ⊓ (T ⊔ B) := le_inf hTQle le_sup_left
  have hXQ : Q ⊓ (T ⊔ B) ≤ Q := inf_le_left
  have hTeven : Even (Nat.card T) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hTQ.isPGroup
    rw [hn] at h4 ⊢
    rcases n with _ | n
    · norm_num at h4
    · exact (Nat.even_pow.mpr ⟨even_two, n.succ_ne_zero⟩)
  have hXeven : Even (Nat.card (Q ⊓ (T ⊔ B) : Subgroup H)) :=
    (even_iff_two_dvd.mpr ((even_iff_two_dvd.mp hTeven).trans (card_dvd_of_le hTX)))
  exact h H B T hiso ⟨hel, h4, hTQle.trans hQN, inf_centralizer_eq_bot_of_not_le_gammaOneOn hΓ⟩
    ⟨Q ⊓ (T ⊔ B), inf_le_right, hTQ.of_le hTX hXQ, hnil.mono hXQ,
      tightlyEmbedded_inf_subgroupOf (sup_le_sup_right hTQle B) htight hXeven⟩

end CFSG.ComponentClassification.AS76b
