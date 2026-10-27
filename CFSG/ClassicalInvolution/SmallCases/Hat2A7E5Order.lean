module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafLieOrder
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafBasic

public section

namespace CFSG.ClassicalInvolution.Hat2A7E5

open CFSG CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatLeaf
  (LieOrderFormulasInput lieOrderDivisor lieOrderNumerator lieSylowExponent lieSylowExponent_pos
    lie_bounds lie_casework)

theorem prime_dvd_card_A7 {p : ℕ} (hp : p.Prime) (h : p ∣ 2520) :
    p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 := by
  rw [show (2520 : ℕ) = 2 ^ 3 * 3 ^ 2 * 5 * 7 by norm_num] at h
  rcases (Nat.Prime.dvd_mul hp).mp h with h | h7
  · rcases (Nat.Prime.dvd_mul hp).mp h with h | h5
    · rcases (Nat.Prime.dvd_mul hp).mp h with h2 | h3
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h2))
      · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp
          (hp.dvd_of_dvd_pow h3)))
    · exact Or.inr (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h5)))
  · exact Or.inr (Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h7)))

theorem lieModel_odd_card_ne_A7 (hO : LieOrderFormulasInput) {X : Type} [Group X]
    {t : StatedLieTag} {n p f : ℕ} (hp2 : p ≠ 2) (hadm : StatedLieAdmissible t n p f)
    (hX : Blueprint.LieModel X t n p f) : Nat.card X ≠ 2520 := by
  intro hc
  have hp : p.Prime := hadm.1
  have hf : 1 ≤ f := hadm.2.1
  have hE := lieSylowExponent_pos hadm
  obtain ⟨-, -, hfac⟩ := hO X t n p f hadm hX
  have hdvd : p ^ (lieSylowExponent t n * f) ∣ 2520 := hc ▸ hfac ▸ Nat.ordProj_dvd _ _
  have hpd : p ∣ 2520 :=
    (dvd_pow_self p (Nat.mul_ne_zero (by omega) (by omega))).trans hdvd
  rcases prime_dvd_card_A7 hp hpd with rfl | rfl | rfl | rfl
  · exact hp2 rfl
  all_goals
    obtain ⟨hb, hord⟩ := lie_bounds hO hadm hX (v := 10) (by rw [hc]; decide)
    rw [hc] at hord
    rcases lie_casework hadm hb with
      ⟨ht, hn1, hn2, hf1, hf2⟩ | ⟨ht, hn1, hn2, hf1, hf2⟩ | ⟨ht, rfl, hf1, hf2⟩
    · rcases ht with rfl | rfl <;> simp only [lieSylowExponent] at hb <;>
        interval_cases n <;> interval_cases f <;> norm_num at hb <;> revert hord <;> decide
    · rcases ht with rfl | rfl <;> simp only [lieSylowExponent] at hb <;>
        interval_cases n <;> interval_cases f <;> norm_num at hb <;> revert hord <;> decide
    · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := ht
      cases t <;> simp only [ne_eq, not_true_eq_false] at h1 h2 h3 h4 h5 h6 <;>
        simp only [lieSylowExponent] at hb <;> interval_cases f <;> norm_num at hb <;>
        revert hord <;> simp only [lieOrderNumerator, lieOrderDivisor] <;> decide

end CFSG.ClassicalInvolution.Hat2A7E5
