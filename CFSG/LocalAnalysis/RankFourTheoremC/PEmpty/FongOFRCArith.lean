module

public import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL.OFRC

variable {p : ℕ}

theorem natCast_pow_prime [Fact p.Prime] (q : ℕ) : ((q ^ p : ℕ) : ZMod p) = (q : ZMod p) := by
  rw [Nat.cast_pow]
  exact ZMod.pow_card _

theorem orderOf_natCast_pow_prime [Fact p.Prime] (q : ℕ) :
    orderOf ((q ^ p : ℕ) : ZMod p) = orderOf (q : ZMod p) := by
  rw [natCast_pow_prime]

theorem orderOf_neg_natCast_pow_prime [Fact p.Prime] (q : ℕ) :
    orderOf (-((q ^ p : ℕ) : ZMod p)) = orderOf (-(q : ZMod p)) := by
  rw [natCast_pow_prime]

theorem dvd_pow_prime_sub_one_iff [Fact p.Prime] {q : ℕ} (hq : 1 ≤ q) :
    p ∣ q ^ p - 1 ↔ p ∣ q - 1 := by
  have h1 : 1 ≤ q ^ p := Nat.one_le_pow _ _ hq
  rw [← ZMod.natCast_eq_zero_iff, ← ZMod.natCast_eq_zero_iff, Nat.cast_sub h1, Nat.cast_sub hq,
    natCast_pow_prime]

theorem dvd_pow_prime_add_one_iff [Fact p.Prime] {q : ℕ} :
    p ∣ q ^ p + 1 ↔ p ∣ q + 1 := by
  rw [← ZMod.natCast_eq_zero_iff, ← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_add,
    natCast_pow_prime]

theorem dvd_add_one_iff_neg_eq_one [Fact p.Prime] (q : ℕ) :
    p ∣ q + 1 ↔ -(q : ZMod p) = 1 := by
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_one]
  exact add_eq_zero_iff_neg_eq

theorem three_div_orderOf_le_one [Fact p.Prime] (z : ZMod p) (hz : z ≠ 1) :
    3 / orderOf z ≤ 1 := by
  rcases Nat.lt_or_ge (orderOf z) 2 with h | h
  · have h1 : orderOf z ≠ 1 := fun h1 => hz (orderOf_eq_one_iff.1 h1)
    have h0 : orderOf z = 0 := by omega
    rw [h0, Nat.div_zero]
    omega
  · have : 3 / orderOf z < 2 := (Nat.div_lt_iff_lt_mul (by omega)).2 (by omega)
    omega

theorem not_dvd_pow_of_ne {ℓ f : ℕ} (hp : p.Prime) (hℓ : ℓ.Prime) (hne : ℓ ≠ p) :
    ¬ p ∣ ℓ ^ f := fun h =>
  hne ((Nat.prime_dvd_prime_iff_eq hp hℓ).1 (hp.dvd_of_dvd_pow h)).symm

theorem natCast_ne_zero_of_not_dvd_card {F : Type} [Field F] [Finite F] (hp : p.Prime)
    (hpF : ¬ p ∣ Nat.card F) : (p : F) ≠ 0 := by
  intro h0
  apply hpF
  haveI : Fintype F := Fintype.ofFinite F
  haveI : CharP F (ringChar F) := ringChar.charP F
  have hℓ : (ringChar F).Prime := CharP.char_is_prime F (ringChar F)
  have h1 : ringChar F ∣ p := (CharP.cast_eq_zero_iff F (ringChar F) p).1 h0
  have h2 : ringChar F = p := (Nat.prime_dvd_prime_iff_eq hℓ hp).1 h1
  obtain ⟨n, -, hn⟩ := FiniteField.card F (ringChar F)
  rw [Nat.card_eq_fintype_card, hn, h2]
  exact dvd_pow_self p n.ne_zero

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL.OFRC
