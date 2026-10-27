module

public import CFSG.LocalAnalysis.AGLEmbedding.BlockFactReductionsIICenter

public section

namespace CFSG.AGLEmbedding.BlockCyc

open CFSG.Blueprint.Multiplier (generic exceptional genericOrders exceptionalOrders)

theorem card_multiplicative_zmod (n : ℕ) : Nat.card (Multiplicative (ZMod n)) = n := by
  rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]

theorem not_five_dvd_card_center_of_alt_five {A : Type} [Group A]
    [Finite A] [Group.IsPerfect A] (e : A ⧸ Subgroup.center A ≃* alternatingGroup (Fin 5)) :
    ¬ 5 ∣ Nat.card (Subgroup.center A) := by
  have hdvd := CFSG.GH74.Generic.card_ker_dvd_hopfMultiplier inferInstance
    (CFSG.GH74.Generic.centralQuotientMap e) (CFSG.GH74.Generic.centralQuotientMap_surjective e)
    (CFSG.GH74.Generic.centralQuotientMap_ker e).le
  rw [CFSG.GH74.Generic.centralQuotientMap_ker e,
    (CFSG.Alternating.Multipliers.schurAlternatingMultiplierInput 5 le_rfl).2] at hdvd
  have h6 : Nat.card (Subgroup.center A) ∣ 6 := by
    split_ifs at hdvd
    · exact hdvd
    · exact hdvd.trans (by norm_num)
  intro h5
  have := h5.trans h6
  omega

theorem not_five_dvd_card_center_of_psl_three (hGA : CFSG.Open.GriessAllModelsStatement)
    {A X : Type} [Group A] [Finite A] [Group.IsPerfect A] [Group X]
    (e : A ⧸ Subgroup.center A ≃* X) {f : ℕ} (hf : 1 ≤ f)
    (hm : CFSG.Models.LieModel X .PSL 3 2 f) : ¬ 5 ∣ Nat.card (Subgroup.center A) := by
  have hdvd := CFSG.GH74.Generic.card_ker_dvd_hopfMultiplier inferInstance
    (CFSG.GH74.Generic.centralQuotientMap e) (CFSG.GH74.Generic.centralQuotientMap_surjective e)
    (CFSG.GH74.Generic.centralQuotientMap_ker e).le
  rw [CFSG.GH74.Generic.centralQuotientMap_ker e] at hdvd
  obtain ⟨-, ⟨g⟩⟩ := hGA X .PSL 3 2 f hm
  have hcard : Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier X) =
      Nat.card (generic .PSL 3 2 f × exceptional .PSL 3 2 f) :=
    Nat.card_congr
      ((CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess X).symm.trans g).toEquiv
  rw [hcard, Nat.card_prod] at hdvd
  have hg : Nat.card (generic .PSL 3 2 f) =
      (genericOrders .PSL 3 2 f).1 * (genericOrders .PSL 3 2 f).2 := by
    unfold generic
    rw [Nat.card_prod, card_multiplicative_zmod, card_multiplicative_zmod]
  have hx : Nat.card (exceptional .PSL 3 2 f) =
      (exceptionalOrders .PSL 3 2 f).1 * (exceptionalOrders .PSL 3 2 f).2 := by
    unfold exceptional
    rw [Nat.card_prod, card_multiplicative_zmod, card_multiplicative_zmod]
  rw [hg, hx, genericOrders_snd_eq_one_of_two .PSL 3 f hf, mul_one] at hdvd
  have h3 : (genericOrders .PSL 3 2 f).1 ∣ 3 := by
    have : (genericOrders .PSL 3 2 f).1 = Nat.gcd 3 (2 ^ f - 1) := by
      simp [genericOrders]
    rw [this]
    exact Nat.gcd_dvd_left _ _
  have h16 := exceptionalOrders_mul_dvd_sixteen_of_two .PSL 3 f
  intro h5
  have h5' := h5.trans hdvd
  rcases (Nat.Prime.dvd_mul (by norm_num)).1 h5' with h | h
  · have := h.trans h3
    omega
  · have := h.trans h16
    omega

end CFSG.AGLEmbedding.BlockCyc
