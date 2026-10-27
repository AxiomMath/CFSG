module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeSporAlt
import CFSG.Sporadic.J3

public section

namespace CFSG.AGLEmbedding

open CFSG.Open

@[expose] def J3CoverWeakGenThree : Prop :=
  @CoverWeakGen (Blueprint.NativeSporadic.Carrier .J3) _ 3 ⟨Nat.prime_three⟩

theorem not_pow_three_dvd_card_J3 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    ¬ p ^ 3 ∣ 50232960 := by
  intro h
  have hd : p ∣ 2 ^ 7 * 3 ^ 5 * 5 * 17 * 19 :=
    (dvd_pow_self p (by norm_num : (3 : ℕ) ≠ 0)).trans (by norm_num at h ⊢; exact h)
  rcases (Nat.Prime.dvd_mul hp).1 hd with hd | h19
  · rcases (Nat.Prime.dvd_mul hp).1 hd with hd | h17
    · rcases (Nat.Prime.dvd_mul hp).1 hd with hd | h5
      · rcases (Nat.Prime.dvd_mul hp).1 hd with h2 | h3'
        · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h2))
        · exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow h3'))
      · rw [(Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).1 h5] at h; norm_num at h
    · rw [(Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 17)).1 h17] at h
      norm_num at h
  · rw [(Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 19)).1 h19] at h; norm_num at h

theorem sporadicCaseThreeDataJ3_of_coverWeakGen
    (h : J3CoverWeakGenThree) :
    SporadicCaseThreeDataJ3 (Blueprint.NativeSporadic.Carrier .J3) := by
  have hc : Nat.card (Blueprint.NativeSporadic.Carrier .J3) = 50232960 :=
    CFSG.Sporadic.J3.card_J3
  refine ⟨by rw [hc]; norm_num, fun {_} => ⟨fun p _ hp2 hp3 => Or.inl ?_, h⟩⟩
  rw [hc]
  exact not_pow_three_dvd_card_J3 Fact.out hp2 hp3

end CFSG.AGLEmbedding
