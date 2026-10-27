module

public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverList

public section

namespace CFSG.AGLEmbedding

open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec4.Census CFSG.RankThree.PerfectCover

@[expose] def sporadicNineList : List TauCeti.SporadicName := [.M22, .McL, .Suz, .Fi22, .Fi24Prime]

structure SporadicMultipliersD1 : Prop where
  big : ∀ (s : TauCeti.SporadicName) (p : ℕ), p.Prime → 5 ≤ p →
    ¬ p ∣ Nat.card (hopfMultiplier (Spor s))
  three : ∀ s : TauCeti.SporadicName, ¬ 3 ∣ sporadicMultiplierOrder s →
    ¬ 3 ∣ Nat.card (hopfMultiplier (Spor s))
  nine : ∀ s ∈ sporadicNineList, ¬ 9 ∣ Nat.card (hopfMultiplier (Spor s))

theorem sporadicMultipliersD1_of_sporadicMultipliers (h : SporadicMultipliers) :
    SporadicMultipliersD1 := by
  refine ⟨fun s p hp hp5 hd => ?_, fun s h3 hd => ?_, fun s hs hd => ?_⟩
  · rw [h.1 s] at hd
    have h12 : p ∣ 12 := hd.trans (by cases s <;> decide)
    have := Nat.le_of_dvd (by norm_num) h12
    clear hd
    interval_cases p <;> revert hp h12 <;> decide
  · rw [h.1 s] at hd
    exact h3 hd
  · rw [h.1 s] at hd
    revert hd hs
    cases s <;> decide

theorem SporadicMultipliersD1.card_center_dvd_three_of_mem (hD : SporadicMultipliersD1) {K : Type}
    [Group K] [Finite K] (hq : CFSG.IsQuasisimple K) (hZ : IsPGroup 3 (Subgroup.center K))
    {s : TauCeti.SporadicName} (hs : s ∈ sporadicNineList)
    (e : K ⧸ Subgroup.center K ≃* Spor s) : Nat.card (Subgroup.center K) ∣ 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hdvd := CFSG.GH74.Generic.card_center_dvd_hopfMultiplier hq e
  obtain ⟨k, hk⟩ := hZ.exists_card_eq
  rw [hk] at hdvd ⊢
  rcases Nat.lt_or_ge k 2 with hk2 | hk2
  · exact (pow_dvd_pow 3 (by omega : k ≤ 1)).trans (by norm_num)
  · exact absurd ((pow_dvd_pow 3 hk2).trans hdvd) (by
      rw [show (3 : ℕ) ^ 2 = 9 by norm_num]; exact hD.nine s hs)

theorem SporadicMultipliersD1.sporadic_cases_of_three_dvd (hD : SporadicMultipliersD1) {K : Type}
    [Group K] [Finite K] (hq : CFSG.IsQuasisimple K) {s : TauCeti.SporadicName}
    (e : K ⧸ Subgroup.center K ≃* Spor s) (h3 : 3 ∣ Nat.card (Subgroup.center K)) :
    s = .M22 ∨ s = .J3 ∨ s = .McL ∨ s = .Suz ∨ s = .ONan ∨ s = .Fi22 ∨ s = .Fi24Prime := by
  have h1 := h3.trans (CFSG.GH74.Generic.card_center_dvd_hopfMultiplier hq e)
  by_contra hs
  refine hD.three s ?_ h1
  clear e h3 hq h1
  revert hs
  cases s <;> decide

end CFSG.AGLEmbedding
