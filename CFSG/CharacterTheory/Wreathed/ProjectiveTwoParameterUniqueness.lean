module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.OrderReductions.LinearOrders

public noncomputable section

namespace CFSG.Wreathed.ProjectiveTwoParameterUniqueness

open CFSG.Assembly.LowTwoRank

theorem card_projective_two_field (K : Type*) [Field K] [Finite K] :
    Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) =
      Nat.card K * (Nat.card K ^ 2 - 1) / Nat.gcd 2 (Nat.card K - 1) := by
  simpa using CFSG.OrderReductions.LinearOrders.card_projectiveSpecialLinear K 2 (by decide)

theorem card_stated_psl_two (G : Type) [Group G] (p f : ℕ)
    (hmodel : StatedClassicalModel G .PSL 2 p f) :
    Nat.card G = p ^ f * ((p ^ f) ^ 2 - 1) / Nat.gcd 2 (p ^ f - 1) := by
  obtain ⟨_, K, hKfield, hKfinite, hKcard, ⟨e⟩⟩ := hmodel
  let := hKfield
  let := hKfinite
  let e' := e.trans (projectiveSpecialLinearGroupEquivStatedProj 2 K).symm
  rw [Nat.card_congr e'.toEquiv, card_projective_two_field, hKcard]

theorem finite_stated_psl_two (G : Type) [Group G] (p f : ℕ)
    (hmodel : StatedClassicalModel G .PSL 2 p f) : Finite G := by
  obtain ⟨_, K, hKfield, hKfinite, _, ⟨e⟩⟩ := hmodel
  let := hKfield
  let := hKfinite
  exact Finite.of_injective e e.injective

theorem card_stated_psl_two_of_odd (G : Type) [Group G] (p f : ℕ)
    (hmodel : StatedClassicalModel G .PSL 2 p f) (hpodd : Odd p) :
    Nat.card G = p ^ f * ((p ^ f) ^ 2 - 1) / 2 := by
  rw [card_stated_psl_two G p f hmodel]
  rw [Nat.gcd_eq_left ((hpodd.pow.tsub_odd odd_one).two_dvd)]

theorem cubic_strictMonoOn :
    StrictMonoOn (fun q : ℕ => q * (q ^ 2 - 1)) (Set.Ici 1) := by
  intro x hx y hy hxy
  have hx1 : 1 ≤ x := hx
  have hy1 : 1 ≤ y := hy
  have hx2 : 1 ≤ x ^ 2 := by nlinarith
  have hy2 : 1 ≤ y ^ 2 := by nlinarith
  have hsx := Nat.sub_add_cancel hx2
  have hsy := Nat.sub_add_cancel hy2
  nlinarith [sq_nonneg ((y : ℤ) - x)]

theorem numerator_even_of_odd {q : ℕ} (hq : Odd q) : 2 ∣ q * (q ^ 2 - 1) := by
  exact dvd_mul_of_dvd_right ((hq.pow.tsub_odd odd_one).two_dvd) q

theorem odd_cubic_quotient_injective {q q' : ℕ} (hq1 : 1 ≤ q) (hq'1 : 1 ≤ q')
    (hqodd : Odd q) (hq'odd : Odd q')
    (horder : q * (q ^ 2 - 1) / 2 = q' * (q' ^ 2 - 1) / 2) : q = q' := by
  have hc : q * (q ^ 2 - 1) = q' * (q' ^ 2 - 1) := by
    have h := congrArg (fun n : ℕ => 2 * n) horder
    rwa [Nat.mul_div_cancel' (numerator_even_of_odd hqodd),
      Nat.mul_div_cancel' (numerator_even_of_odd hq'odd)] at h
  exact cubic_strictMonoOn.injOn hq1 hq'1 hc

theorem stated_psl_two_parameters_unique (G : Type) [Group G] (p f r a : ℕ)
    (hp : p.Prime) (hr : r.Prime) (hpodd : Odd p) (hrodd : Odd r)
    (hf : 1 ≤ f) (ha : 1 ≤ a) (hq5 : 5 ≤ p ^ f)
    (hmodel : StatedClassicalModel G .PSL 2 p f)
    (hmodel' : StatedClassicalModel G .PSL 2 r a) :
    r ^ a = p ^ f ∧ r = p ∧ a = f := by
  have hcard := (card_stated_psl_two_of_odd G r a hmodel' hrodd).symm.trans
    (card_stated_psl_two_of_odd G p f hmodel hpodd)
  have hq : r ^ a = p ^ f := odd_cubic_quotient_injective
    (Nat.one_le_pow a r hr.one_le) (by omega) hrodd.pow hpodd.pow hcard
  have hparams := hr.pow_inj' hp (by omega) (by omega) hq
  exact ⟨hq, hparams.1, hparams.2⟩

theorem stated_psl_two_order_and_parameter_uniqueness (G : Type) [Group G] (p f : ℕ)
    (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq5 : 5 ≤ p ^ f)
    (hmodel : StatedClassicalModel G .PSL 2 p f) :
    Finite G ∧ Nat.card G = p ^ f * ((p ^ f) ^ 2 - 1) / 2 ∧
      ∀ (r a : ℕ), r.Prime → Odd r → 1 ≤ a →
        StatedClassicalModel G .PSL 2 r a → r ^ a = p ^ f ∧ r = p ∧ a = f := by
  refine ⟨finite_stated_psl_two G p f hmodel,
    card_stated_psl_two_of_odd G p f hmodel hpodd, ?_⟩
  intro r a hr hrodd ha hmodel'
  exact stated_psl_two_parameters_unique G p f r a hp hr hpodd hrodd hf ha hq5
    hmodel hmodel'

end CFSG.Wreathed.ProjectiveTwoParameterUniqueness
