module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P54Defs
public import CFSG.RankThree.PerfectCover.HopfFormula
public import CFSG.RankThree.PerfectCover.HopfCentralCoversSetup
public import CFSG.Blueprint.MultiplierDefs

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.P54

open CFSG Subgroup Assembly.LowTwoRank Blueprint.Multiplier

@[expose] def GriessNativeTable : Prop :=
  ∀ (X : Type) [Group X] (t : StatedLieTag) (n p f : ℕ), Blueprint.LieModel X t n p f →
    commutator X = ⊤ ∧
      Nonempty (Open.griessHopfMultiplier X ≃* generic t n p f × exceptional t n p f)

theorem card_multiplicative_zmod (a : ℕ) : Nat.card (Multiplicative (ZMod a)) = a := by
  rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]

theorem card_generic_prod_exceptional (t : StatedLieTag) (n p f : ℕ) :
    Nat.card (generic t n p f × exceptional t n p f) =
      (genericOrders t n p f).1 * (genericOrders t n p f).2 *
        ((exceptionalOrders t n p f).1 * (exceptionalOrders t n p f).2) := by
  simp only [generic, exceptional, Nat.card_prod, card_multiplicative_zmod]

theorem odd_card_table {τ : StatedLieTag} {n p f : ℕ} (hR : oddR τ n) (hp2 : p ≠ 2)
    (h5 : 5 ≤ p ^ f) :
    Odd ((genericOrders τ n p f).1 * (genericOrders τ n p f).2 *
      ((exceptionalOrders τ n p f).1 * (exceptionalOrders τ n p f).2)) := by
  have hex : exceptionalOrders τ n p f = (1, 1) := by
    rcases hR with ⟨hτ | hτ, hn⟩ | hτ | hτ | hτ | hτ | hτ | hτ | hτ | hτ | hτ | hτ <;>
      subst hτ <;> unfold exceptionalOrders <;> split <;> simp_all [Nat.odd_iff]
  have hg : Odd (genericOrders τ n p f).1 ∧ Odd (genericOrders τ n p f).2 := by
    have h3 : ∀ m : ℕ, Odd (Nat.gcd 3 m) := fun m => Odd.of_dvd_nat (by decide)
      (Nat.gcd_dvd_left 3 m)
    rcases hR with ⟨hτ | hτ, hn⟩ | hτ | hτ | hτ | hτ | hτ | hτ | hτ | hτ | hτ | hτ <;>
      subst hτ <;> simp only [genericOrders]
    · exact ⟨Odd.of_dvd_nat hn (Nat.gcd_dvd_left _ _), odd_one⟩
    · exact ⟨Odd.of_dvd_nat hn (Nat.gcd_dvd_left _ _), odd_one⟩
    all_goals first
      | exact ⟨odd_one, odd_one⟩
      | exact ⟨h3 _, odd_one⟩
  rw [hex]
  exact (hg.1.mul hg.2).mul (by decide)

theorem rowOdd (hG : GriessNativeTable) : RowOdd := by
  intro Y _ _ hq hZ p hp hp2 τ n f hR hlie h5 hpsl hc t ht htZ
  exfalso
  obtain ⟨-, ⟨eM⟩⟩ := hG _ τ n p f hlie
  have hodd : Odd (Nat.card (Open.griessHopfMultiplier (Y ⧸ center Y))) := by
    rw [Nat.card_congr eM.toEquiv, card_generic_prod_exceptional]
    exact odd_card_table hR hp2 h5
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

end CFSG.ComponentClassification.HarrisLit.T1.P54
