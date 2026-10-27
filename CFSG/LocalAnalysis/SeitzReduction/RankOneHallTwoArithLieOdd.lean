module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrderArith
public import CFSG.LocalAnalysis.SeitzReduction.RankOneHallTwoArithLieOddClassical
public import CFSG.LocalAnalysis.SeitzReduction.RankOneHallTwoArithLieOddExceptional

public section

namespace CFSG.SeitzReduction.RankOne

open CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
  CFSG.ComponentClassification.CatLeafProof

namespace LieOdd

theorem two_mul_add_three_le_two_pow {e : ℕ} (he : 4 ≤ e) : 2 * e + 3 ≤ 2 ^ e := by
  induction e, he using Nat.le_induction with
  | base => norm_num
  | succ e he ih =>
    rw [pow_succ]
    omega

theorem psl_two_eq_seven {q e h : ℕ} (hq : 3 ≤ q) (hq3 : q ≠ 3) (hqodd : Odd q)
    (heq : q * (q ^ 2 - 1) = 2 ^ e * h * 2) (he1 : 1 ≤ e) (hdiv : h ∣ (2 ^ e - 1) * e) :
    q = 7 := by
  have hsq : q ^ 2 - 1 = (q - 1) * (q + 1) := by
    rw [show q ^ 2 - 1 = q ^ 2 - 1 ^ 2 by norm_num, Nat.sq_sub_sq, mul_comm]
  have hne : q ^ 2 - 1 ≠ 0 := by
    rw [hsq]
    exact mul_ne_zero (by omega) (by omega)
  have hdvd : 2 ^ (e + 1) ∣ q ^ 2 - 1 := by
    have : 2 ^ (e + 1) ∣ q * (q ^ 2 - 1) := by
      rw [heq, pow_succ]
      exact ⟨h, by ring⟩
    exact ((Nat.coprime_two_left.mpr hqodd).pow_left (e + 1)).dvd_of_dvd_mul_left this
  have h2e : 2 ^ (e + 1) ≤ 2 * (q + 1) := by
    have h1 := Nat.pow_le_pow_right two_pos
      ((Nat.prime_two.pow_dvd_iff_le_factorization hne).mp hdvd)
    rw [hsq, Nat.ordProj_mul 2 (by omega) (by omega)] at h1
    exact h1.trans (ordProj_sub_one_mul_ordProj_add_one_le hq hqodd)
  have h2e' : 2 ^ e ≤ q + 1 := by
    rw [pow_succ] at h2e
    omega
  have h2 : 2 ≤ 2 ^ e :=
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he1
  have hh : h ≤ (2 ^ e - 1) * e := Nat.le_of_dvd (Nat.mul_pos (by omega) (by omega)) hdiv
  have h3 : q * (q - 1) ≤ 2 * h := by
    have : q * (q - 1) * (q + 1) ≤ 2 * h * (q + 1) :=
      calc q * (q - 1) * (q + 1) = q * (q ^ 2 - 1) := by rw [hsq]; ring
        _ = 2 ^ (e + 1) * h := by rw [heq, pow_succ]; ring
        _ ≤ 2 * (q + 1) * h := Nat.mul_le_mul_right _ h2e
        _ = 2 * h * (q + 1) := by ring
    exact Nat.le_of_mul_le_mul_right this (by omega)
  have h4 : h ≤ q * e := hh.trans (Nat.mul_le_mul_right _ (by omega))
  have h5 : q - 1 ≤ 2 * e := by
    have : q * (q - 1) ≤ q * (2 * e) :=
      calc q * (q - 1) ≤ 2 * h := h3
        _ ≤ 2 * (q * e) := Nat.mul_le_mul_left _ h4
        _ = q * (2 * e) := by ring
    exact Nat.le_of_mul_le_mul_left this (by omega)
  have h6 : e ≤ 3 := by
    by_contra h6
    have := two_mul_add_three_le_two_pow (e := e) (by omega)
    omega
  obtain ⟨k, rfl⟩ := hqodd
  rcases (by omega : k = 2 ∨ k = 3) with rfl | rfl
  · exfalso
    rw [show (2 * 2 + 1) * ((2 * 2 + 1) ^ 2 - 1) = 120 by norm_num] at heq
    exact false_of_two_pow_mul_eq (c := 60) (E := 2) (by omega) (by norm_num) (by norm_num) he1
      hdiv
  · rfl

theorem false_of_lieOrder {n g c E e h : ℕ} (hn : n = 2 ^ e * h * g) (hc : n = c * g)
    (hg : 0 < g) (hE : ¬ 2 ^ (E + 1) ∣ c) (hlt : 2 ^ E * (2 ^ E - 1) * E < c) (he1 : 1 ≤ e)
    (hdiv : h ∣ (2 ^ e - 1) * e) : False :=
  false_of_two_pow_mul_eq (Nat.eq_of_mul_eq_mul_right hg (hn.symm.trans hc)) hE hlt he1 hdiv

theorem eq_psl_two_seven_of_lie_odd {t : StatedLieTag} {m p f e h : ℕ}
    (hadm : StatedLieAdmissible t m p f) (hp2 : p ≠ 2)
    (hnum : lieOrderNumerator t m (p ^ f) = 2 ^ e * h * lieOrderDivisor t m (p ^ f))
    (he1 : 1 ≤ e) (hdiv : h ∣ (2 ^ e - 1) * e) :
    t = .PSL ∧ m = 2 ∧ p = 7 ∧ f = 1 := by
  have hp : p.Prime := hadm.1
  have hpodd : Odd p := hp.eq_two_or_odd'.resolve_left hp2
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    rcases hpodd with ⟨k, hk⟩
    omega
  have hq : 3 ≤ p ^ f := le_trans hp3 (Nat.le_self_pow (by have := hadm.2.1; omega) p)
  have hqodd : Odd (p ^ f) := hpodd.pow
  have hnum' := hnum
  rw [lieOrderNumerator_eq hadm] at hnum'
  have hodd35 : p ^ f < 7 → p ^ f = 3 ∨ p ^ f = 5 := fun h7 => by
    rcases hqodd with ⟨k, hk⟩
    omega
  cases t with
  | PSL =>
    obtain ⟨-, -, hm2, -, hne23⟩ := hadm
    simp only [lieSylowExponent, lieOrderCofactor, lieOrderDivisor] at hnum'
    rcases (by omega : m = 2 ∨ 3 ≤ m) with rfl | hm3
    · have hq3 : p ^ f ≠ 3 := fun h3 => hne23 (by rw [h3])
      have hg2 : Nat.gcd 2 (p ^ f - 1) = 2 :=
        Nat.gcd_eq_left (even_iff_two_dvd.mp (Nat.Odd.sub_odd hqodd odd_one))
      rw [hg2] at hnum'
      have hq7 : p ^ f = 7 := psl_two_eq_seven hq hq3 hqodd (by simpa using hnum') he1 hdiv
      obtain ⟨hp7, hf1⟩ := (Nat.Prime.pow_eq_iff (by norm_num)).mp hq7
      exact ⟨rfl, rfl, hp7, hf1⟩
    · exfalso
      rcases lieOdd_typeA (fun i => (p ^ f) ^ i - 1)
          (fun i hi => twoPartBound_pow_sub_one' hq hqodd hi) hq hqodd hm3 hnum'
          (Nat.gcd_le_left _ (by omega)) he1 hdiv with ⟨rfl, hlt⟩ | ⟨rfl, hlt⟩
      · rcases hodd35 hlt with h3 | h3 <;> rw [h3] at hnum
        · exact false_of_lieOrder (c := 5616) (E := 4) hnum (by decide) (by decide)
            (by norm_num) (by norm_num) he1 hdiv
        · exact false_of_lieOrder (c := 372000) (E := 5) hnum (by decide) (by decide)
            (by norm_num) (by norm_num) he1 hdiv
      · have h3 : p ^ f = 3 := by rcases hqodd with ⟨k, hk⟩; omega
        rw [h3] at hnum
        exact false_of_lieOrder (c := 6065280) (E := 7) hnum (by decide) (by decide)
          (by norm_num) (by norm_num) he1 hdiv
  | PSU =>
    obtain ⟨-, -, hm3, -⟩ := hadm
    simp only [lieSylowExponent, lieOrderCofactor, lieOrderDivisor] at hnum'
    exfalso
    rcases lieOdd_typeA (fun i => if Even i then (p ^ f) ^ i - 1 else (p ^ f) ^ i + 1)
        (fun i hi => twoPartBound_psu_factor hq hqodd hi) hq hqodd hm3 hnum'
        (Nat.gcd_le_left _ (by omega)) he1 hdiv with ⟨rfl, hlt⟩ | ⟨rfl, hlt⟩
    · rcases hodd35 hlt with h3 | h3 <;> rw [h3] at hnum
      · exact false_of_lieOrder (c := 6048) (E := 5) hnum (by decide) (by decide)
          (by norm_num) (by norm_num) he1 hdiv
      · exact false_of_lieOrder (c := 126000) (E := 4) hnum (by decide) (by decide)
          (by norm_num) (by norm_num) he1 hdiv
    · have h3 : p ^ f = 3 := by rcases hqodd with ⟨k, hk⟩; omega
      rw [h3] at hnum
      exact false_of_lieOrder (c := 3265920) (E := 7) hnum (by decide) (by decide)
        (by norm_num) (by norm_num) he1 hdiv
  | PSp =>
    obtain ⟨-, -, hm2, -⟩ := hadm
    simp only [lieSylowExponent, lieOrderCofactor, lieOrderDivisor] at hnum'
    exfalso
    obtain ⟨rfl, hlt⟩ := lieOdd_typeB hq hqodd hm2 hnum' (Nat.gcd_le_left _ (by norm_num)) he1
      hdiv
    rcases hodd35 hlt with h3 | h3 <;> rw [h3] at hnum
    · exact false_of_lieOrder (c := 25920) (E := 6) hnum (by decide) (by decide)
        (by norm_num) (by norm_num) he1 hdiv
    · exact false_of_lieOrder (c := 4680000) (E := 6) hnum (by decide) (by decide)
        (by norm_num) (by norm_num) he1 hdiv
  | POmegaOdd =>
    obtain ⟨-, -, hm3, -⟩ := hadm
    simp only [lieSylowExponent, lieOrderCofactor, lieOrderDivisor] at hnum'
    exfalso
    have := (lieOdd_typeB hq hqodd (by omega) hnum' le_rfl he1 hdiv).1
    omega
  | POmegaPlus =>
    obtain ⟨-, -, hm4⟩ := hadm
    simp only [lieSylowExponent, lieOrderCofactor, lieOrderDivisor] at hnum'
    exact (lieOdd_typeC hq hqodd hm4 (twoPartBound_pow_sub_one' hq hqodd (by omega)) hnum'
      (Nat.gcd_le_left _ (by norm_num)) he1 hdiv).elim
  | POmegaMinus =>
    obtain ⟨-, -, hm4⟩ := hadm
    simp only [lieSylowExponent, lieOrderCofactor, lieOrderDivisor] at hnum'
    exact (lieOdd_typeC hq hqodd hm4 ((twoPartBound_pow_add_one hq hqodd (by omega)).mono le_rfl
      (Nat.le_mul_of_pos_right _ (by positivity))) hnum'
      (Nat.gcd_le_left _ (by norm_num)) he1 hdiv).elim
  | G2 =>
    simp only [lieSylowExponent, lieOrderCofactor, lieOrderDivisor] at hnum'
    exact (false_G2 hq hqodd hnum' le_rfl he1 hdiv).elim
  | F4 =>
    simp only [lieSylowExponent, lieOrderCofactor, lieOrderDivisor] at hnum'
    exact (false_F4 hq hqodd hnum' le_rfl he1 hdiv).elim
  | E6 =>
    simp only [lieSylowExponent, lieOrderCofactor, lieOrderDivisor] at hnum'
    exact (false_E6 hq hqodd hnum' (Nat.gcd_le_left _ (by norm_num)) he1 hdiv).elim
  | E7 =>
    simp only [lieSylowExponent, lieOrderCofactor, lieOrderDivisor] at hnum'
    exact (false_E7 hq hqodd hnum' (Nat.gcd_le_left _ (by norm_num)) he1 hdiv).elim
  | E8 =>
    simp only [lieSylowExponent, lieOrderCofactor, lieOrderDivisor] at hnum'
    exact (false_E8 hq hqodd hnum' le_rfl he1 hdiv).elim
  | twistedE6 =>
    simp only [lieSylowExponent, lieOrderCofactor, lieOrderDivisor] at hnum'
    exact (false_twistedE6 hq hqodd hnum' (Nat.gcd_le_left _ (by norm_num)) he1 hdiv).elim
  | trialityD4 =>
    simp only [lieSylowExponent, lieOrderCofactor, lieOrderDivisor] at hnum'
    exact (false_trialityD4 hq hqodd hnum' le_rfl he1 hdiv).elim
  | twistedG2 =>
    obtain ⟨-, -, -, hp3', -, hf3⟩ := hadm
    simp only [lieSylowExponent, lieOrderCofactor, lieOrderDivisor] at hnum'
    have hq5 : 5 ≤ p ^ f := by
      rw [hp3']
      calc 5 ≤ 3 ^ 3 := by norm_num
        _ ≤ 3 ^ f := Nat.pow_le_pow_right (by norm_num) hf3
    exact (false_twistedG2 hq5 hqodd hnum' le_rfl he1 hdiv).elim
  | twistedB2 =>
    obtain ⟨-, -, -, hp2', -⟩ := hadm
    exact absurd hp2' hp2
  | twistedF4 =>
    obtain ⟨-, -, -, hp2', -⟩ := hadm
    exact absurd hp2' hp2
  | Tits =>
    obtain ⟨-, -, -, hp2', -⟩ := hadm
    exact absurd hp2' hp2

end LieOdd

end CFSG.SeitzReduction.RankOne
