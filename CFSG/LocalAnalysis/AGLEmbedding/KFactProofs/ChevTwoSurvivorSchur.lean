module

public import CFSG.LocalAnalysis.AGLEmbedding.ChevTwoSurvivorSocle
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CenterHopf
import CFSG.LieType.Steinberg.CentralExt.GriessClassicalSmall
import CFSG.LieType.Steinberg.CentralExt.GriessReeF4
import CFSG.RankThree.PartTwo.Census.Carrier.SpinBBridge
public import CFSG.Blueprint.MultiplierDefs
public import CFSG.Open.GriessSchurMultipliersMilestoneDefs

public section

namespace CFSG.AGLEmbedding

open CFSG.Assembly.LowTwoRank CFSG.Blueprint.Multiplier
open CFSG.LieType.Steinberg.CentralExt

private theorem card_of_row {X : Type} [Group X] {t : StatedLieTag} {n p f : ℕ}
    (h : Nonempty (CFSG.Open.griessHopfMultiplier X ≃* generic t n p f × exceptional t n p f)) :
    Nat.card (CFSG.Open.griessHopfMultiplier X) =
      (genericOrders t n p f).1 * (genericOrders t n p f).2 *
        ((exceptionalOrders t n p f).1 * (exceptionalOrders t n p f).2) := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv, Nat.card_prod]
  unfold generic exceptional
  simp only [Nat.card_prod, Nat.card_congr (Multiplicative.toAdd : _ ≃ _), Nat.card_zmod]

private theorem genericOrders_psp_two_two_three : genericOrders .PSp 2 2 3 = (1, 1) := by
  change (Nat.gcd 2 (2 ^ 3 - 1), 1) = (1, 1)
  norm_num

private theorem exceptionalOrders_psp_two_two_three : exceptionalOrders .PSp 2 2 3 = (1, 1) := by
  unfold exceptionalOrders
  split <;> simp_all

private theorem genericOrders_psp_three_two_one : genericOrders .PSp 3 2 1 = (1, 1) := by
  change (Nat.gcd 2 (2 ^ 1 - 1), 1) = (1, 1)
  norm_num

private theorem exceptionalOrders_psp_three_two_one : exceptionalOrders .PSp 3 2 1 = (2, 1) := rfl

private theorem genericOrders_g2 : genericOrders .G2 0 2 3 = (1, 1) := rfl

private theorem exceptionalOrders_g2 : exceptionalOrders .G2 0 2 3 = (1, 1) := by
  unfold exceptionalOrders
  split <;> simp_all

private theorem genericOrders_twistedF4 : genericOrders .twistedF4 0 2 5 = (1, 1) := rfl

private theorem exceptionalOrders_twistedF4 : exceptionalOrders .twistedF4 0 2 5 = (1, 1) := by
  unfold exceptionalOrders
  split <;> simp_all

theorem survivor_prime_and_not_dvd {p : ℕ} {d : TauCeti.ValidLieTypeIndex}
    (hd : IsChevTwoSurvivorIndex p d) :
    p.Prime ∧ ¬ p ∣ Nat.card (CFSG.Open.griessHopfMultiplier (CatGroup d)) := by
  obtain ⟨d1, hv⟩ := d
  rcases hd with ⟨rfl, q, hqp, hqe, hd1⟩ | ⟨rfl, q, hqp, hqe, hd1⟩ | ⟨rfl, q, hqp, hqe, hd1⟩ |
    ⟨rfl, hd1⟩
  · simp only at hd1
    subst hd1
    refine ⟨Nat.prime_three, ?_⟩
    have hcl := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even 3 q hv hqp le_rfl
      (G := CatGroup ⟨.B 3 q, hv⟩) (MulEquiv.refl _)
    rw [hqp, hqe] at hcl
    obtain ⟨-, ⟨e⟩⟩ := GriessClassical.psp_three_two_row (X := CatGroup ⟨.B 3 q, hv⟩)
      ⟨hcl.1, Or.inl hcl⟩
    rw [card_of_row ⟨e⟩, genericOrders_psp_three_two_one, exceptionalOrders_psp_three_two_one]
    norm_num
  · simp only at hd1
    subst hd1
    refine ⟨Nat.prime_three, ?_⟩
    have hcl := CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv
      (G := CatGroup ⟨.B 2 q, hv⟩) (MulEquiv.refl _)
    rw [hqp, hqe] at hcl
    obtain ⟨-, ⟨e⟩⟩ := GriessClassical.psp_row hcl (Or.inl (by norm_num))
    rw [card_of_row ⟨e⟩, genericOrders_psp_two_two_three, exceptionalOrders_psp_two_two_three]
    norm_num
  · simp only at hd1
    subst hd1
    refine ⟨Nat.prime_three, ?_⟩
    have hmodel : CFSG.Models.LieModel (CatGroup ⟨.G2 q, hv⟩) .G2 0 2 3 :=
      ⟨⟨Nat.prime_two, by norm_num, rfl, by norm_num⟩,
        Or.inr ⟨rfl, ⟨.G2 q, hv⟩, ⟨hqp, hqe⟩, ⟨MulEquiv.refl _⟩⟩⟩
    obtain ⟨-, ⟨e⟩⟩ := GriessExceptional.g2_row hmodel (by norm_num)
    rw [card_of_row ⟨e⟩, genericOrders_g2, exceptionalOrders_g2]
    norm_num
  · simp only at hd1
    subst hd1
    refine ⟨Nat.prime_five, ?_⟩
    have hmodel : CFSG.Models.LieModel (CatGroup ⟨.reeF4 2, hv⟩) .twistedF4 0 2 5 :=
      ⟨⟨Nat.prime_two, by norm_num, rfl, rfl, by decide, by norm_num⟩,
        Or.inr ⟨rfl, ⟨.reeF4 2, hv⟩, ⟨rfl, rfl⟩, ⟨MulEquiv.refl _⟩⟩⟩
    obtain ⟨-, ⟨e⟩⟩ := GriessExceptional.twistedF4_row hmodel
    rw [card_of_row ⟨e⟩, genericOrders_twistedF4, exceptionalOrders_twistedF4]
    norm_num

theorem kFactChevTwoSurvivorSchur : KFactChevTwoSurvivorSchur := by
  intro K _ _ p d hd hq hp ⟨e⟩
  obtain ⟨hprime, hnd⟩ := survivor_prime_and_not_dvd hd
  have : Fact p.Prime := ⟨hprime⟩
  have hdvd := card_center_dvd_card_griessHopfMultiplier ⟨hq.1⟩ e
  obtain ⟨k, hk⟩ := hp.exists_card_eq
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · exact Subgroup.card_eq_one.mp (by simpa using hk)
  · exact absurd ((dvd_pow_self p hk0.ne').trans (hk ▸ hdvd)) hnd

end CFSG.AGLEmbedding
