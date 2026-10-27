module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafInputs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanOuterSylowStep
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafBasic

public section

namespace CFSG.AGLEmbedding.OuterSylow

open CFSG.Assembly.LowTwoRank (StatedLieTag)
open CFSG.ComponentClassification.CatLeaf (lieOrderNumerator lieSylowExponent)

section Step

variable {p : ℕ} [Fact p.Prime]

theorem exists_stp_numerator (hodd : Odd p) {t : StatedLieTag} {n q : ℕ} (ht : t ≠ .Tits)
    (ht3 : t ≠ .trialityD4) (hN : 1 ≤ lieSylowExponent t n) (hq : 2 ≤ q) :
    ∃ k, Stp p (lieOrderNumerator t n q) (lieOrderNumerator t n (q ^ p)) k := by
  have hp3 : 3 ≤ p := by
    have h2 := (Fact.out : p.Prime).two_le
    rcases hodd with ⟨r, hr⟩
    omega
  have hq1 : 1 ≤ q := by omega
  cases t with
  | PSL =>
    simp only [lieSylowExponent] at hN
    refine Stp.mul' ⟨_, Stp.pow_q hp3 hq1 hN⟩ (Stp.prod' _ fun i hi => ?_)
    exact ⟨_, Stp.sub_pow hodd hq (by have := Finset.mem_Icc.1 hi; omega)⟩
  | PSU =>
    simp only [lieSylowExponent] at hN
    refine Stp.mul' ⟨_, Stp.pow_q hp3 hq1 hN⟩ (Stp.prod' _ fun i hi => ?_)
    have hi1 : 1 ≤ i := by have := Finset.mem_Icc.1 hi; omega
    by_cases he : Even i
    · simp only [he, ↓reduceIte]
      exact ⟨_, Stp.sub_pow hodd hq hi1⟩
    · simp only [he, ↓reduceIte]
      exact ⟨_, Stp.add_pow hodd hq1⟩
  | PSp =>
    simp only [lieSylowExponent] at hN
    refine Stp.mul' ⟨_, Stp.pow_q hp3 hq1 hN⟩ (Stp.prod' _ fun i hi => ?_)
    exact ⟨_, Stp.sub_pow hodd hq (by have := Finset.mem_Icc.1 hi; omega)⟩
  | POmegaOdd =>
    simp only [lieSylowExponent] at hN
    refine Stp.mul' ⟨_, Stp.pow_q hp3 hq1 hN⟩ (Stp.prod' _ fun i hi => ?_)
    exact ⟨_, Stp.sub_pow hodd hq (by have := Finset.mem_Icc.1 hi; omega)⟩
  | POmegaPlus =>
    simp only [lieSylowExponent] at hN
    have hn : 1 ≤ n := by
      rcases Nat.eq_zero_or_pos n with rfl | h
      · simp at hN
      · exact h
    refine Stp.mul' (Stp.mul' ⟨_, Stp.pow_q hp3 hq1 hN⟩ ⟨_, Stp.sub_pow hodd hq hn⟩)
      (Stp.prod' _ fun i hi => ?_)
    exact ⟨_, Stp.sub_pow hodd hq (by have := Finset.mem_Icc.1 hi; omega)⟩
  | POmegaMinus =>
    simp only [lieSylowExponent] at hN
    refine Stp.mul' (Stp.mul' ⟨_, Stp.pow_q hp3 hq1 hN⟩ ⟨_, Stp.add_pow hodd hq1⟩)
      (Stp.prod' _ fun i hi => ?_)
    exact ⟨_, Stp.sub_pow hodd hq (by have := Finset.mem_Icc.1 hi; omega)⟩
  | G2 =>
    exact ⟨_, ((Stp.pow_q hp3 hq1 (N := 6) (by norm_num)).mul (Stp.sub_pow' hodd hq 6)).mul
      (Stp.sub_pow' hodd hq 2)⟩
  | F4 =>
    exact ⟨_, ((((Stp.pow_q hp3 hq1 (N := 24) (by norm_num)).mul (Stp.sub_pow' hodd hq 12)).mul
      (Stp.sub_pow' hodd hq 8)).mul (Stp.sub_pow' hodd hq 6)).mul (Stp.sub_pow' hodd hq 2)⟩
  | E6 =>
    exact ⟨_, ((((((Stp.pow_q hp3 hq1 (N := 36) (by norm_num)).mul
      (Stp.sub_pow' hodd hq 12)).mul (Stp.sub_pow' hodd hq 9)).mul
      (Stp.sub_pow' hodd hq 8)).mul (Stp.sub_pow' hodd hq 6)).mul
      (Stp.sub_pow' hodd hq 5)).mul (Stp.sub_pow' hodd hq 2)⟩
  | E7 =>
    exact ⟨_, (((((((Stp.pow_q hp3 hq1 (N := 63) (by norm_num)).mul
      (Stp.sub_pow' hodd hq 18)).mul (Stp.sub_pow' hodd hq 14)).mul
      (Stp.sub_pow' hodd hq 12)).mul (Stp.sub_pow' hodd hq 10)).mul
      (Stp.sub_pow' hodd hq 8)).mul (Stp.sub_pow' hodd hq 6)).mul (Stp.sub_pow' hodd hq 2)⟩
  | E8 =>
    exact ⟨_, ((((((((Stp.pow_q hp3 hq1 (N := 120) (by norm_num)).mul
      (Stp.sub_pow' hodd hq 30)).mul (Stp.sub_pow' hodd hq 24)).mul
      (Stp.sub_pow' hodd hq 20)).mul (Stp.sub_pow' hodd hq 18)).mul
      (Stp.sub_pow' hodd hq 14)).mul (Stp.sub_pow' hodd hq 12)).mul
      (Stp.sub_pow' hodd hq 8)).mul (Stp.sub_pow' hodd hq 2)⟩
  | twistedE6 =>
    exact ⟨_, ((((((Stp.pow_q hp3 hq1 (N := 36) (by norm_num)).mul
      (Stp.sub_pow' hodd hq 12)).mul (Stp.add_pow' hodd hq1 9)).mul
      (Stp.sub_pow' hodd hq 8)).mul (Stp.sub_pow' hodd hq 6)).mul
      (Stp.add_pow' hodd hq1 5)).mul (Stp.sub_pow' hodd hq 2)⟩
  | trialityD4 => exact absurd rfl ht3
  | twistedB2 =>
    exact ⟨_, ((Stp.pow_q hp3 hq1 (N := 2) (by norm_num)).mul (Stp.add_pow' hodd hq1 2)).mul
      (Stp.sub_one hodd hq)⟩
  | twistedG2 =>
    exact ⟨_, ((Stp.pow_q hp3 hq1 (N := 3) (by norm_num)).mul (Stp.add_pow' hodd hq1 3)).mul
      (Stp.sub_one hodd hq)⟩
  | twistedF4 =>
    exact ⟨_, ((((Stp.pow_q hp3 hq1 (N := 12) (by norm_num)).mul (Stp.add_pow' hodd hq1 6)).mul
      (Stp.sub_pow' hodd hq 4)).mul (Stp.add_pow' hodd hq1 3)).mul (Stp.sub_one hodd hq)⟩
  | Tits => exact absurd rfl ht

end Step

theorem numerator_factorization_lt {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {t : StatedLieTag}
    {n q : ℕ} (ht : t ≠ .Tits) (ht3 : t ≠ .trialityD4) (hN : 1 ≤ lieSylowExponent t n)
    (hq : 2 ≤ q) (h : p ∣ lieOrderNumerator t n (q ^ p)) :
    (lieOrderNumerator t n q).factorization p <
      (lieOrderNumerator t n (q ^ p)).factorization p := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := exists_stp_numerator (p := p) (hp.odd_of_ne_two hp2) ht ht3 hN hq
  rw [Nat.factorization_def _ hp, Nat.factorization_def _ hp]
  exact hk.valuation_lt h

end CFSG.AGLEmbedding.OuterSylow
