module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTable
public import CFSG.Open.GriessAllModelsStatement
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsLie
import CFSG.RankThree.PartOne.N143.Inspect613Even
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
import CFSG.Adapters.StatedClassicalUnitaryOrders
import CFSG.Adapters.StatedClassicalSmallOrders
import CFSG.Quasithin.Background.F918G2
import CFSG.HardMathSupport.Timmesfeld.Tables.Alt.Rank

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.RankThree.PerfectCover CFSG.Blueprint.Multiplier CFSG.Models CFSG.Assembly.LowTwoRank

namespace RankSmall

theorem one_le_pRank_of_prime_dvd {G : Type*} [Group G] [Finite G] {r : ℕ} (hr : r.Prime)
    (h : r ∣ Nat.card G) : 1 ≤ CFSG.Open.pRank r (⊤ : Subgroup G) := by
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' r h
  refine CFSG.SectionRank.le_pRank hr.one_lt (le_top : Subgroup.zpowers x ≤ ⊤) ⟨inferInstance, ?_⟩ ?_
  · rintro y ⟨k, rfl⟩
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hx, pow_orderOf_eq_one,
      one_zpow]
  · rw [Nat.card_zpowers, hx, pow_one]

theorem pRank_top_eq_of_card {G : Type*} [Group G] [Finite G] {r N : ℕ} (hr : r.Prime)
    (hN : Nat.card G = N) (h2 : ¬ r ^ 2 ∣ N) :
    CFSG.Open.pRank r (⊤ : Subgroup G) = if r ∣ N then 1 else 0 := by
  by_cases hd : r ∣ N
  · rw [if_pos hd]
    refine le_antisymm ?_ (one_le_pRank_of_prime_dvd hr (hN ▸ hd))
    exact CFSG.HardMathSupport.Timmesfeld.Tables.Alt.pRank_top_le_of_not_dvd (k := 1) hr.one_lt
      (by rwa [hN])
  · rw [if_neg hd]
    refine Nat.le_zero.1 ?_
    exact CFSG.HardMathSupport.Timmesfeld.Tables.Alt.pRank_top_le_of_not_dvd (k := 0) hr.one_lt
      (by rw [hN]; simpa using hd)

theorem prime_dvd_168 {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) :
    (r ∣ 168 ↔ r = 3 ∨ r = 7) ∧ ¬ r ^ 2 ∣ 168 := by
  have key : r ∣ 168 → r = 3 ∨ r = 7 := by
    intro h
    have h' : r ∣ 2 ^ 3 * 3 * 7 := by norm_num; exact h
    rcases (Nat.Prime.dvd_mul hr).1 h' with h1 | h1
    · rcases (Nat.Prime.dvd_mul hr).1 h1 with h2 | h2
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow h2)) hr2
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).1 h2)
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hr (by norm_num)).1 h1)
  refine ⟨⟨key, ?_⟩, ?_⟩
  · rintro (rfl | rfl) <;> norm_num
  · intro h
    rcases key (dvd_trans (dvd_pow_self r (by norm_num)) h) with rfl | rfl <;> norm_num at h

theorem prime_dvd_6048 {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hr3 : r ≠ 3) :
    (r ∣ 6048 ↔ r = 7) ∧ ¬ r ^ 2 ∣ 6048 := by
  have key : r ∣ 6048 → r = 7 := by
    intro h
    have h' : r ∣ 2 ^ 5 * 3 ^ 3 * 7 := by norm_num; exact h
    rcases (Nat.Prime.dvd_mul hr).1 h' with h1 | h1
    · rcases (Nat.Prime.dvd_mul hr).1 h1 with h2 | h2
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow h2)) hr2
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).1 (hr.dvd_of_dvd_pow h2)) hr3
    · exact (Nat.prime_dvd_prime_iff_eq hr (by norm_num)).1 h1
  refine ⟨⟨key, ?_⟩, ?_⟩
  · rintro rfl; norm_num
  · intro h
    have := key (dvd_trans (dvd_pow_self r (by norm_num)) h)
    subst this
    norm_num at h

end RankSmall

theorem lieOddRankSmall_of_griess (hG : CFSG.Open.GriessAllModelsStatement) : LieOddRankSmall := by
  intro K _ _ hq r hr hr2
  haveI : Fact r.Prime := ⟨hr⟩
  refine ⟨?_, ?_⟩
  · rintro ⟨q, ⟨d1, hv⟩, hq7, hd, ⟨e⟩⟩
    simp only at hd
    subst hd
    have hm := CFSG.RankThree.PartOne.N143.statedClassicalModel_of_isoLie_A hv e
    obtain ⟨hp7, he1⟩ := (Nat.Prime.pow_eq_iff (by norm_num : Nat.Prime 7)).mp (ksm_card_eq hq7)
    rw [hp7, he1] at hm
    have hLM : LieModel (K ⧸ Subgroup.center K) .PSL (1 + 1) 7 1 := ⟨hm.1, Or.inl hm⟩
    have hdvd := ksm_card_center_dvd hG hq hLM
    have hgen : genericOrders .PSL (1 + 1) 7 1 = (2, 1) := by
      show (Nat.gcd (1 + 1) (7 ^ 1 - 1), 1) = (2, 1)
      norm_num
    have hexc : exceptionalOrders .PSL (1 + 1) 7 1 = (1, 1) := by
      unfold exceptionalOrders
      split <;> first | rfl | simp_all
    rw [hgen, hexc] at hdvd
    have hZ2 : Nat.card (Subgroup.center K) ∣ 2 := by simpa using hdvd
    have hrZ : ¬ r ∣ Nat.card (Subgroup.center K) := fun h => by
      have := Nat.le_of_dvd (by norm_num) (h.trans hZ2)
      have := hr.two_le
      omega
    rw [← CFSG.SectionRank.pRank_quotient_eq (Subgroup.center K) hrZ]
    have hcard : Nat.card (K ⧸ Subgroup.center K) = 168 :=
      CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_two_seven hm
    obtain ⟨h168, hsq⟩ := RankSmall.prime_dvd_168 hr hr2
    rw [RankSmall.pRank_top_eq_of_card hr hcard hsq]
    simp only [h168]
  · rintro ⟨q, ⟨d1, hv⟩, hq3, hd, ⟨e⟩⟩
    simp only at hd
    subst hd
    have hm := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv e
    obtain ⟨hp3, he1⟩ := (Nat.Prime.pow_eq_iff Nat.prime_three).mp (ksm_card_eq hq3)
    rw [hp3, he1] at hm
    have hLM : LieModel (K ⧸ Subgroup.center K) .PSU (2 + 1) 3 1 := ⟨hm.1, Or.inl hm⟩
    have hdvd := ksm_card_center_dvd hG hq hLM
    have hgen : genericOrders .PSU (2 + 1) 3 1 = (1, 1) := by
      show (Nat.gcd (2 + 1) (3 ^ 1 + 1), 1) = (1, 1)
      norm_num
    have hexc : exceptionalOrders .PSU (2 + 1) 3 1 = (1, 1) := by
      unfold exceptionalOrders
      split <;> first | rfl | simp_all
    rw [hgen, hexc] at hdvd
    have hZ1 : Nat.card (Subgroup.center K) ∣ 1 := by simpa using hdvd
    have hrZ : ¬ r ∣ Nat.card (Subgroup.center K) := fun h => by
      have := Nat.le_of_dvd (by norm_num) (h.trans hZ1)
      have := hr.two_le
      omega
    rw [← CFSG.SectionRank.pRank_quotient_eq (Subgroup.center K) hrZ]
    have hcard : Nat.card (K ⧸ Subgroup.center K) = 6048 :=
      CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_three_three hm
    by_cases hr3 : r = 3
    · subst hr3
      simp only [if_true]
      exact CFSG.Quasithin.pRank_three_psu33 hm
    · obtain ⟨h6048, hsq⟩ := RankSmall.prime_dvd_6048 hr hr2 hr3
      rw [RankSmall.pRank_top_eq_of_card hr hcard hsq, if_neg hr3]
      by_cases hr7 : r = 7
      · subst hr7; simp
      · simp [h6048, hr7]

end CFSG.LocalAnalysis.RankThreeUC.S15
