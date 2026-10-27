module

public import CFSG.Milestones.CL_LIT_Griess_Schur_multipliers_Lie_type
public import CFSG.RankThree.PerfectCover.HopfFormula

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I923

open CFSG.RankThree.PerfectCover CFSG.Blueprint.Multiplier

theorem card_multiplicative_zmod (n : ℕ) : Nat.card (Multiplicative (ZMod n)) = n := by
  rw [Nat.card_congr Multiplicative.toAdd]
  exact Nat.card_zmod n

section


theorem card_hopfMultiplier_e6 {X : Type} [Group X] {p f : ℕ}
    (hX : CFSG.Blueprint.LieModel X .E6 0 p f) :
    Nat.card (hopfMultiplier X) = Nat.gcd 3 (p ^ f - 1) := by
  obtain ⟨-, ⟨e⟩⟩ := CFSG.Milestones.cl_lit_griess_schur_multipliers_all_native_models X .E6 0 p f hX
  rw [← Nat.card_congr (hopfMultiplierEquivGriess X).toEquiv, Nat.card_congr e.toEquiv,
    Nat.card_prod, Nat.card_prod, Nat.card_prod]
  simp [genericOrders, exceptionalOrders, card_multiplicative_zmod]

theorem card_hopfMultiplier_twistedE6 {X : Type} [Group X] {p f : ℕ}
    (hX : CFSG.Blueprint.LieModel X .twistedE6 0 p f) :
    Nat.card (hopfMultiplier X) =
      Nat.gcd 3 (p ^ f + 1) * (if p = 2 ∧ f = 1 then 4 else 1) := by
  obtain ⟨-, ⟨e⟩⟩ := CFSG.Milestones.cl_lit_griess_schur_multipliers_all_native_models X
    .twistedE6 0 p f hX
  rw [← Nat.card_congr (hopfMultiplierEquivGriess X).toEquiv, Nat.card_congr e.toEquiv,
    Nat.card_prod, Nat.card_prod, Nat.card_prod]
  by_cases h : p = 2 ∧ f = 1
  · obtain ⟨rfl, rfl⟩ := h
    simp [genericOrders, exceptionalOrders, card_multiplicative_zmod]
  · have h2 : exceptionalOrders .twistedE6 0 p f = (1, 1) := by
      unfold exceptionalOrders
      split <;> first | rfl | (exfalso; simp_all)
    simp [genericOrders, h2, card_multiplicative_zmod, h]

theorem not_nine_dvd_hopfMultiplier_e6 {X : Type} [Group X] {p f : ℕ}
    (hX : CFSG.Blueprint.LieModel X .E6 0 p f) : ¬ 9 ∣ Nat.card (hopfMultiplier X) := by
  rw [card_hopfMultiplier_e6 hX]
  intro h9
  have h3 : Nat.gcd 3 (p ^ f - 1) ∣ 3 := Nat.gcd_dvd_left _ _
  have := Nat.le_of_dvd (by norm_num) (h9.trans h3)
  omega

theorem not_nine_dvd_hopfMultiplier_twistedE6 {X : Type} [Group X] {p f : ℕ}
    (hX : CFSG.Blueprint.LieModel X .twistedE6 0 p f) :
    ¬ 9 ∣ Nat.card (hopfMultiplier X) := by
  rw [card_hopfMultiplier_twistedE6 hX]
  intro h9
  have h3 : Nat.gcd 3 (p ^ f + 1) ∣ 3 := Nat.gcd_dvd_left _ _
  rcases Nat.Prime.eq_one_or_self_of_dvd Nat.prime_three _ h3 with h | h
  · rw [h, one_mul] at h9
    split_ifs at h9 <;> omega
  · rw [h] at h9
    split_ifs at h9 <;> omega

end

end CFSG.HardMathSupport.Dickson.Sec6.I923
