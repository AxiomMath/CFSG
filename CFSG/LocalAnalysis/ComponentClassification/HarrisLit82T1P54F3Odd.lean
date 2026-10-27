module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P54F3Defs
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P54Odd

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.P54.F3

open CFSG Subgroup Assembly.LowTwoRank Blueprint.Multiplier

theorem odd_card_table_three {τ : StatedLieTag} {n : ℕ} (hR : oddR τ n) :
    Odd ((genericOrders τ n 3 1).1 * (genericOrders τ n 3 1).2 *
      ((exceptionalOrders τ n 3 1).1 * (exceptionalOrders τ n 3 1).2)) := by
  have hex : Odd ((exceptionalOrders τ n 3 1).1 * (exceptionalOrders τ n 3 1).2) := by
    rcases hR with ⟨hτ | hτ, hn⟩ | hτ | hτ | hτ | hτ | hτ | hτ | hτ | hτ | hτ | hτ <;>
      subst hτ <;> unfold exceptionalOrders <;> split <;> simp_all [Nat.odd_iff]
  have hg : Odd (genericOrders τ n 3 1).1 ∧ Odd (genericOrders τ n 3 1).2 := by
    rcases hR with ⟨hτ | hτ, hn⟩ | hτ | hτ | hτ | hτ | hτ | hτ | hτ | hτ | hτ | hτ <;>
      subst hτ <;> simp only [genericOrders]
    · exact ⟨Odd.of_dvd_nat hn (Nat.gcd_dvd_left _ _), odd_one⟩
    · exact ⟨Odd.of_dvd_nat hn (Nat.gcd_dvd_left _ _), odd_one⟩
    all_goals exact ⟨odd_one, odd_one⟩
  exact (hg.1.mul hg.2).mul hex

theorem rowOddThree (hG : GriessNativeTable) : RowOddThree := by
  intro Y _ _ hq hZ τ n hR hlie hc t ht htZ
  exfalso
  obtain ⟨-, ⟨eM⟩⟩ := hG _ τ n 3 1 hlie
  have hodd : Odd (Nat.card (Open.griessHopfMultiplier (Y ⧸ center Y))) := by
    rw [Nat.card_congr eM.toEquiv, card_generic_prod_exceptional]
    exact odd_card_table_three hR
  have : Group.IsPerfect Y := hq.1
  have hdvd := Subgroup.card_dvd_of_surjective
    (RankThree.PerfectCover.hopfMultiplierToKer_surjective (QuotientGroup.mk' (center Y))
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' (center Y)).le)
  rw [← Nat.card_congr (RankThree.PerfectCover.hopfMultiplierEquivGriess _).toEquiv,
    QuotientGroup.ker_mk'] at hdvd
  have h2 : 2 ∣ Nat.card (center Y) := by
    have h := orderOf_dvd_natCard (⟨t, htZ⟩ : center Y)
    rwa [Subgroup.orderOf_mk, ht] at h
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr (h2.trans hdvd))

end CFSG.ComponentClassification.HarrisLit.T1.P54.F3
