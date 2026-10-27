module

public import CFSG.Timmesfeld.ARS.CaseHFinal
public import CFSG.Timmesfeld.Final.Orders

public section

namespace CFSG.CGT.T75O

open CFSG.Timmesfeld CFSG.Timmesfeld.ARS CFSG.Timmesfeld.ARS.CaseH CFSG.Blueprint
  CFSG.Assembly.LowTwoRank CFSG.Open

theorem odd_two_pow_sub_one {j : ℕ} (hj : j ≠ 0) : Odd (2 ^ j - 1) :=
  Nat.Even.sub_odd (Nat.one_le_two_pow) ((Nat.even_pow).2 ⟨even_two, hj⟩) odd_one

theorem ordG2_two_pow {f : ℕ} (hf : f ≠ 0) :
    ∃ o : ℕ, Odd o ∧ ordG2 (2 ^ f) = 2 ^ (6 * f) * o := by
  refine ⟨((2 ^ f) ^ 6 - 1) * ((2 ^ f) ^ 2 - 1), Odd.mul ?_ ?_, ?_⟩
  · rw [← pow_mul]
    exact odd_two_pow_sub_one (by omega)
  · rw [← pow_mul]
    exact odd_two_pow_sub_one (by omega)
  · unfold ordG2
    rw [← pow_mul, mul_comm f 6]
    ring

theorem ordTrialityD4_two_pow {f : ℕ} (hf : f ≠ 0) :
    ∃ o : ℕ, Odd o ∧ ordTrialityD4 (2 ^ f) = 2 ^ (12 * f) * o := by
  refine ⟨(((2 ^ f) ^ 8 + (2 ^ f) ^ 4 + 1) * ((2 ^ f) ^ 6 - 1)) * ((2 ^ f) ^ 2 - 1),
    Odd.mul (Odd.mul ?_ ?_) ?_, ?_⟩
  · have h8 : Even ((2 ^ f) ^ 8) := by
      rw [← pow_mul]
      exact (Nat.even_pow).2 ⟨even_two, by omega⟩
    have h4 : Even ((2 ^ f) ^ 4) := by
      rw [← pow_mul]
      exact (Nat.even_pow).2 ⟨even_two, by omega⟩
    exact (h8.add h4).add_one
  · rw [← pow_mul]
    exact odd_two_pow_sub_one (by omega)
  · rw [← pow_mul]
    exact odd_two_pow_sub_one (by omega)
  · unfold ordTrialityD4
    rw [← pow_mul, mul_comm f 12]
    ring


variable {G : Type} [Group G] {R : Set (Subgroup G)} {A A₀ P P' : Subgroup G}
  {S : Setup R A A₀ P P'} {F E : Type} [Field F] [Field E] (c : Coords S F E) [CharP E 2]
  [CharP F 2] [Finite F] [Finite E] (e : F →+* E) (he : ∀ s u, c.c5 s u = c.c5 (e u * s) 1)
  {τ : F} (hτ0 : τ ≠ 0) (hτ : ∀ u, c.m * c.x6 u * c.m⁻¹ = c.x2 (τ * u))

include he hτ0 hτ in
theorem card_g2 (hsq : ∀ s, c.sharp s = s ^ 2) (hEF : Nat.card E = Nat.card F) {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 2 ≤ n) : ∃ o : ℕ, Odd o ∧ Nat.card G = 2 ^ (6 * n) * o := by
  have := S.hyp.finite
  obtain ⟨F', _, _, hF', φ, hc, hgen, hnt⟩ := c.g2Frame e he hτ0 hτ hsq hEF hF hn
  have hq : 3 ≤ 2 ^ n := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hn)
  obtain ⟨-, -, -, -, hmodel⟩ := exists_lieModel_of_coneCompatible_G2 Nat.prime_two (by omega)
    hq hF' S.hyp.center hc hgen hnt
  have hch := Final.chevalleyExceptionalModel_of_lieModel (by decide) hmodel
  rw [ExceptionalOrders.card_of_untwistedChevalleyModel_G2 hch.2]
  exact ordG2_two_pow (by omega)

include he hτ0 hτ in
theorem card_d4 {n : ℕ} (hsq : ∀ s, c.sharp s = s ^ (2 ^ n + 2 ^ (2 * n)))
    (hF : Nat.card F = 2 ^ n) (hE : Nat.card E = 2 ^ (3 * n)) (hn : 1 ≤ n) :
    ∃ o : ℕ, Odd o ∧ Nat.card G = 2 ^ (12 * n) * o := by
  have := S.hyp.finite
  obtain ⟨F', _, _, hF', σ, hσ, φ, hc, hgen, hnt⟩ := c.d4Frame e he hτ0 hτ hsq hF hE hn
  obtain ⟨-, -, -, -, hmodel⟩ := exists_lieModel_of_coneCompatible_twistedD4 Nat.prime_two hn hF'
    σ hσ S.hyp.center hc hgen hnt
  have hch := Final.chevalleyExceptionalModel_of_lieModel (by decide) hmodel
  have h : Nat.card G = ordTrialityD4 (2 ^ n) := card_chevalleyExceptionalModel_two hch
  rw [h]
  exact ordTrialityD4_two_pow (by omega)

end CFSG.CGT.T75O
