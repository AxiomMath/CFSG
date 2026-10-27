module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1SporNum

public section

namespace CFSG.ComponentClassification.HarrisLit.T1.SporRow

open CFSG Assembly.LowTwoRank CatLeaf

private lemma three_dvd_of_mul_eq_of_not_dvd {m d N : ℕ} (h : m * d = N) (hN : 3 ∣ N)
    (hd : ¬ 3 ∣ d) : 3 ∣ m := by
  rw [← h] at hN
  exact ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hd).dvd_of_dvd_mul_right hN

private lemma three_dvd_of_sq_dvd_mul {m d e N : ℕ} (h : m * d = N) (hd : 0 < d)
    (hde : d ∣ e) (h3e : 3 ∣ e) (heN : e ^ 2 ∣ N) : 3 ∣ m := by
  have hdvd : 3 * d ∣ e * e := Nat.mul_dvd_mul h3e hde
  rw [pow_two] at heN
  have hN : 3 * d ∣ N := hdvd.trans heN
  rw [← h] at hN
  exact Nat.dvd_of_mul_dvd_mul_right hd hN

theorem three_dvd_of_exceptional {τ : StatedLieTag} {n p f m : ℕ}
    (ha : StatedLieAdmissible τ n p f)
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 ∨ τ = .twistedE6 ∨ τ = .trialityD4)
    (hq : ¬ 3 ∣ p ^ f)
    (h : m * lieOrderDivisor τ n (p ^ f) = lieOrderNumerator τ n (p ^ f)) : 3 ∣ m := by
  have h3 : 3 ∣ (p ^ f) ^ 2 - 1 := three_dvd_sq_sub_one hq
  rcases hτ with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  ·
    rw [show lieOrderDivisor .G2 n (p ^ f) = 1 from rfl, mul_one] at h
    rw [h]
    simp only [lieOrderNumerator]
    exact dvd_mul_of_dvd_right h3 _
  ·
    rw [show lieOrderDivisor .F4 n (p ^ f) = 1 from rfl, mul_one] at h
    rw [h]
    simp only [lieOrderNumerator]
    exact dvd_mul_of_dvd_right h3 _
  ·
    rw [show lieOrderDivisor .E6 n (p ^ f) = Nat.gcd 3 (p ^ f - 1) from rfl] at h
    by_cases h3d : 3 ∣ Nat.gcd 3 (p ^ f - 1)
    ·
      refine three_dvd_of_sq_dvd_mul h
        (Nat.gcd_pos_of_pos_left (p ^ f - 1) (by norm_num : 0 < 3))
        (Nat.gcd_dvd_right 3 (p ^ f - 1)) (h3d.trans (Nat.gcd_dvd_right 3 (p ^ f - 1))) ?_
      have hfac : ((p ^ f) ^ 5 - 1) * ((p ^ f) ^ 2 - 1) ∣
          lieOrderNumerator .E6 n (p ^ f) := by
        simp only [lieOrderNumerator]
        exact mul_dvd_mul (dvd_mul_left _ _) dvd_rfl
      rw [show (p ^ f - 1) ^ 2 = (p ^ f - 1) * (p ^ f - 1) from pow_two _]
      exact (mul_dvd_mul (Nat.sub_one_dvd_pow_sub_one (p ^ f) 5)
        (Nat.sub_one_dvd_pow_sub_one (p ^ f) 2)).trans hfac
    ·
      refine three_dvd_of_mul_eq_of_not_dvd h ?_ h3d
      show 3 ∣ lieOrderNumerator .E6 n (p ^ f)
      simp only [lieOrderNumerator]
      exact dvd_mul_of_dvd_right h3 _
  ·
    rw [show lieOrderDivisor .E7 n (p ^ f) = Nat.gcd 2 (p ^ f - 1) from rfl] at h
    refine three_dvd_of_mul_eq_of_not_dvd h ?_ ?_
    · show 3 ∣ lieOrderNumerator .E7 n (p ^ f)
      simp only [lieOrderNumerator]
      exact dvd_mul_of_dvd_right h3 _
    · intro h3d
      have h32 : 3 ∣ 2 := h3d.trans (Nat.gcd_dvd_left 2 (p ^ f - 1))
      norm_num at h32
  ·
    rw [show lieOrderDivisor .E8 n (p ^ f) = 1 from rfl, mul_one] at h
    rw [h]
    simp only [lieOrderNumerator]
    exact dvd_mul_of_dvd_right h3 _
  ·
    rw [show lieOrderDivisor .twistedE6 n (p ^ f) = Nat.gcd 3 (p ^ f + 1) from rfl] at h
    by_cases h3d : 3 ∣ Nat.gcd 3 (p ^ f + 1)
    ·
      refine three_dvd_of_sq_dvd_mul h
        (Nat.gcd_pos_of_pos_left (p ^ f + 1) (by norm_num : 0 < 3))
        (Nat.gcd_dvd_right 3 (p ^ f + 1)) (h3d.trans (Nat.gcd_dvd_right 3 (p ^ f + 1))) ?_
      have hfac : ((p ^ f) ^ 5 + 1) * ((p ^ f) ^ 2 - 1) ∣
          lieOrderNumerator .twistedE6 n (p ^ f) := by
        simp only [lieOrderNumerator]
        exact mul_dvd_mul (dvd_mul_left _ _) dvd_rfl
      rw [show (p ^ f + 1) ^ 2 = (p ^ f + 1) * (p ^ f + 1) from pow_two _]
      refine (mul_dvd_mul ?_ ?_).trans hfac
      · have hodd := Odd.nat_add_dvd_pow_add_pow (x := p ^ f) (y := 1) (n := 5)
          (by decide : Odd 5)
        simpa using hodd
      · have hsq : (p ^ f) ^ 2 - 1 ^ 2 = (p ^ f + 1) * (p ^ f - 1) :=
          Nat.sq_sub_sq (p ^ f) 1
        exact ⟨p ^ f - 1, by simpa using hsq⟩
    ·
      refine three_dvd_of_mul_eq_of_not_dvd h ?_ h3d
      show 3 ∣ lieOrderNumerator .twistedE6 n (p ^ f)
      simp only [lieOrderNumerator]
      exact dvd_mul_of_dvd_right h3 _
  ·
    rw [show lieOrderDivisor .trialityD4 n (p ^ f) = 1 from rfl, mul_one] at h
    rw [h]
    simp only [lieOrderNumerator]
    exact dvd_mul_of_dvd_right h3 _

end CFSG.ComponentClassification.HarrisLit.T1.SporRow
