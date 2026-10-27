module

public import CFSG.FeitThompson.Definitions.ElementaryAbelianPRank
import CFSG.FeitThompson.Local.RankTwoAutomorphismLinearQuotient
import CFSG.FeitThompson.Local.GeneralLinearTwoPrimeFieldOrder

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Matrix Subgroup

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p q n : ℕ} {P : Type*} [Group P]

theorem prime_lt_of_dvd_card_of_odd_of_elementaryAbelianPRank_le_two [Finite P] (hp : p.Prime)
    (hpodd : Odd p) (hP : IsPGroup p P) (hrank : elementaryAbelianPRank p P ≤ 2)
    {A : Subgroup (MulAut P)} (hA : Odd (Nat.card ↥A)) (hq : q.Prime) (hqp : q ≠ p)
    (hqA : q ∣ Nat.card ↥A) : q < p := by
  have := Fact.mk hp
  have hp3 : 3 ≤ p := by
    obtain ⟨k, hk⟩ := hpodd
    have := hp.two_le
    omega
  have hq2 := hq.two_le
  have hqodd : Odd q := hA.of_dvd_nat hqA
  rcases subsingleton_or_nontrivial P with hPs | hPn
  ·
    have : Subsingleton (MulAut P) := ⟨fun a b => MulEquiv.ext fun x => Subsingleton.elim _ _⟩
    have hcard : Nat.card ↥A = 1 := Nat.card_eq_one_iff_unique.2 ⟨inferInstance, inferInstance⟩
    rw [hcard] at hqA
    exact absurd (Nat.eq_one_of_dvd_one hqA) hq.one_lt.ne'
  obtain ⟨B, hBnormal, d, hBp, hd, f, hf⟩ :=
    exists_normal_isPGroup_injective_quotient_toGL_of_elementaryAbelianPRank_le_two hp hpodd hP
      hrank A
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hBp
  have hqQ : q ∣ Nat.card (↥A ⧸ B) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup B, hk] at hqA
    rcases (Nat.Prime.dvd_mul hq).1 hqA with h | h
    · exact h
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hq hp).1 (hq.dvd_of_dvd_pow h)) hqp
  have hdvd : q ∣ Nat.card (GL (Fin d) (ZMod p)) :=
    hqQ.trans (Subgroup.card_dvd_of_injective f hf)
  have key : q ∣ p - 1 ∨ q ∣ p + 1 := by
    rcases hd with rfl | rfl
    · rw [card_GL_one_zmod] at hdvd
      exact Or.inl hdvd
    · rw [card_GL_two_zmod_factored, mul_assoc] at hdvd
      rcases (Nat.Prime.dvd_mul hq).1 hdvd with h | h
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hq hp).1 h) hqp
      · rcases (Nat.Prime.dvd_mul hq).1 h with h | h
        · exact Or.inl (hq.dvd_of_dvd_pow h)
        · exact Or.inr h
  rcases key with h | h
  · have := Nat.le_of_dvd (by omega) h
    omega
  ·
    have h2 : 2 ∣ p + 1 := hpodd.add_one.two_dvd
    have := Nat.le_of_dvd (by omega)
      ((Nat.coprime_two_left.2 hqodd).mul_dvd_of_dvd_of_dvd h2 h)
    omega

theorem prime_lt_of_dvd_card_of_odd_of_card_eq_pow (hp : p.Prime) (hpodd : Odd p)
    (hcard : Nat.card P = p ^ n) (hrank : elementaryAbelianPRank p P ≤ 2)
    {A : Subgroup (MulAut P)} (hA : Odd (Nat.card ↥A)) (hq : q.Prime) (hqp : q ≠ p)
    (hqA : q ∣ Nat.card ↥A) : q < p := by
  have : Finite P := Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ hp.pos.ne')
  exact prime_lt_of_dvd_card_of_odd_of_elementaryAbelianPRank_le_two hp hpodd
    (IsPGroup.of_card hcard) hrank hA hq hqp hqA

theorem prime_le_of_dvd_card_of_odd_of_elementaryAbelianPRank_le_two [Finite P] (hp : p.Prime)
    (hpodd : Odd p) (hP : IsPGroup p P) (hrank : elementaryAbelianPRank p P ≤ 2)
    {A : Subgroup (MulAut P)} (hA : Odd (Nat.card ↥A)) (hq : q.Prime)
    (hqA : q ∣ Nat.card ↥A) : q ≤ p := by
  rcases eq_or_ne q p with rfl | hqp
  · exact le_rfl
  · exact (prime_lt_of_dvd_card_of_odd_of_elementaryAbelianPRank_le_two hp hpodd hP hrank hA hq hqp
      hqA).le

end

end CFSG.FeitThompson
