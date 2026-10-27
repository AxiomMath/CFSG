module

public import CFSG.Open.GriessAllModelsStatement
public import CFSG.RankThree.PerfectCover.HopfCentralCoversFinite
public import CFSG.RankThree.PerfectCover.HopfFormula

public section

namespace CFSG.LocalAnalysis.GLTheoremA.YS04G

open CFSG.Open CFSG.Blueprint.Multiplier CFSG.Assembly.LowTwoRank CFSG.RankThree.PerfectCover

theorem not_dvd_exceptional_orders {t : StatedLieTag} (ht : t = .PSL ∨ t = .PSU)
    {n p' f p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpn : p ∣ n) (hn : 3 ≤ n) :
    ¬ p ∣ (exceptionalOrders t n p' f).1 * (exceptionalOrders t n p' f).2 := by
  have h2 : ∀ k : ℕ, p ∣ 2 ^ k → False := fun k h =>
    hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h))
  rcases ht with rfl | rfl <;> unfold exceptionalOrders <;> split <;> simp_all
  all_goals first
    | exact hp.one_lt.ne'
    | exact fun h => h2 1 (by simpa using h)
    | exact fun h => h2 2 (by simpa using h)
    | exact fun h => hp.one_lt.ne' (Nat.dvd_one.1 (by have := Nat.dvd_gcd hpn h; simpa using this))

theorem card_multiplicative_zmod (k : ℕ) : Nat.card (Multiplicative (ZMod k)) = k := by
  rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod k) ≃ ZMod k), Nat.card_zmod]

theorem card_generic (t : StatedLieTag) (n p' f : ℕ) :
    Nat.card (generic t n p' f) =
      (genericOrders t n p' f).1 * (genericOrders t n p' f).2 := by
  simp only [generic, Nat.card_prod, card_multiplicative_zmod]

theorem card_exceptional (t : StatedLieTag) (n p' f : ℕ) :
    Nat.card (exceptional t n p' f) =
      (exceptionalOrders t n p' f).1 * (exceptionalOrders t n p' f).2 := by
  simp only [exceptional, Nat.card_prod, card_multiplicative_zmod]

theorem finite_hopf_of_model (hG : GriessAllModelsStatement) {X : Type} [Group X] [Finite X]
    {t : StatedLieTag} {n p' f : ℕ} (hmodel : CFSG.Models.LieModel X t n p' f) :
    Finite (hopfMultiplier X) :=
  finite_hopfMultiplier (Group.isPerfect_def.2 (hG X t n p' f hmodel).1)

theorem hopf_factorization_le (hG : GriessAllModelsStatement) {X : Type} [Group X] [Finite X]
    {t : StatedLieTag} {n p' f : ℕ} (hmodel : CFSG.Models.LieModel X t n p' f)
    (ht : t = .PSL ∨ t = .PSU) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpn : p ∣ n) (hn : 3 ≤ n)
    {g : ℕ} (hg : genericOrders t n p' f = (g, 1)) (hg0 : g ≠ 0)
    [Finite (hopfMultiplier X)] :
    (Nat.card (hopfMultiplier X)).factorization p ≤ g.factorization p := by
  obtain ⟨-, ⟨eM⟩⟩ := hG X t n p' f hmodel
  have hcard : Nat.card (hopfMultiplier X) =
      Nat.card (generic t n p' f × exceptional t n p' f) :=
    Nat.card_congr ((hopfMultiplierEquivGriess X).symm.toEquiv.trans eM.toEquiv)
  rw [Nat.card_prod, card_generic, card_exceptional, hg] at hcard
  have hab := not_dvd_exceptional_orders (p' := p') (f := f) ht hp hp2 hpn hn
  have hab0 : (exceptionalOrders t n p' f).1 * (exceptionalOrders t n p' f).2 ≠ 0 := by
    intro h0
    rw [h0] at hab
    exact hab (dvd_zero p)
  rw [hcard, Nat.factorization_mul (by simpa using hg0) hab0]
  simp only [Finsupp.add_apply, mul_one]
  rw [Nat.factorization_eq_zero_of_not_dvd hab]
  simp

end CFSG.LocalAnalysis.GLTheoremA.YS04G
