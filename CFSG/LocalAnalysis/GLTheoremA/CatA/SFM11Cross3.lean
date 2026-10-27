module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.SFM11Arith

public section

namespace CFSG.LocalAnalysis.GLTheoremA.SFM11

theorem fac3_mul {A B : ℕ} (hA : A ≠ 0) (hB : B ≠ 0) :
    (A * B).factorization 3 = A.factorization 3 + B.factorization 3 := by
  simp [Nat.factorization_mul hA hB]

theorem fac3_pow (A k : ℕ) : (A ^ k).factorization 3 = k * A.factorization 3 := by
  simp [Nat.factorization_pow]

theorem three_dvd_x {s x : ℕ} (hs3 : ¬ 3 ∣ s) (hx : s ^ 2 = x + 1) : 3 ∣ x := by
  have hsm : s % 3 = 1 ∨ s % 3 = 2 := by omega
  have h2 : s ^ 2 % 3 = 1 := by
    rcases hsm with h | h <;> simp [Nat.pow_mod, h]
  omega

theorem three_dvd_facts {x : ℕ} (h3x : 3 ∣ x) :
    ¬ 3 ∣ x + 2 ∧ ¬ 3 ∣ x * (x + 2) + 2 ∧ (x ^ 2 + 3 * x + 3).factorization 3 = 1 := by
  obtain ⟨m, rfl⟩ := h3x
  refine ⟨?_, ?_, ?_⟩
  · omega
  · have e : 3 * m * (3 * m + 2) + 2 = 3 * (3 * (m * m) + 2 * m) + 2 := by ring
    rw [e]
    omega
  · have e : (3 * m) ^ 2 + 3 * (3 * m) + 3 = 3 * (3 * m ^ 2 + 3 * m + 1) := by ring
    have h0 : (3 * m ^ 2 + 3 * m + 1).factorization 3 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd (by omega)
    have h3 : (3 : ℕ).factorization 3 = 1 := Nat.Prime.factorization_self Nat.prime_three
    have hm : (3 * m ^ 2 + 3 * m + 1) ≠ 0 := by omega
    rw [e, fac3_mul (by norm_num) hm, h0, h3]

theorem cross_p3_B {M s a d : ℕ} (hs2 : 2 ≤ s) (hs3 : ¬ 3 ∣ s) (hd : d ∣ 4) (hd1 : 1 ≤ d)
    (hfac : M.factorization 3 = 6 * a)
    (E2 : M * d = s ^ 9 * ((s ^ 2 - 1) * ((s ^ 4 - 1) * (s ^ 6 - 1)))) : False := by
  obtain ⟨x, hx⟩ : ∃ x, s ^ 2 = x + 1 :=
    ⟨s ^ 2 - 1, by have : 1 ≤ s ^ 2 := Nat.one_le_pow _ _ (by omega); omega⟩
  obtain ⟨hx2, hx4, hx6, -, -⟩ := sq_facts hx
  have h3x : 3 ∣ x := three_dvd_x hs3 hx
  obtain ⟨hn2, -, hC⟩ := three_dvd_facts h3x
  have hx1 : 1 ≤ x := by nlinarith
  have E2' : M * d = s ^ 9 * (x ^ 3 * ((x + 2) * (x ^ 2 + 3 * x + 3))) := by
    rw [E2, hx2, hx4, hx6]
    ring
  have hx0 : x ≠ 0 := by omega
  have hC0 : x ^ 2 + 3 * x + 3 ≠ 0 := by omega
  have hx20 : x + 2 ≠ 0 := by omega
  have hFY0 : x ^ 3 * ((x + 2) * (x ^ 2 + 3 * x + 3)) ≠ 0 :=
    mul_ne_zero (pow_ne_zero 3 hx0) (mul_ne_zero hx20 hC0)
  have hM0 : M ≠ 0 := by
    rintro rfl
    rw [zero_mul] at E2'
    exact mul_ne_zero (pow_ne_zero 9 (by omega)) hFY0 E2'.symm
  have hd0 : d ≠ 0 := by omega
  have hs0 : s ≠ 0 := by omega
  have hsf : s.factorization 3 = 0 := Nat.factorization_eq_zero_of_not_dvd hs3
  have hdf : d.factorization 3 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd fun h => by
      have := h.trans hd
      norm_num at this
  have hxn2 : (x + 2).factorization 3 = 0 := Nat.factorization_eq_zero_of_not_dvd hn2
  have eA : (M * d).factorization 3 = M.factorization 3 + d.factorization 3 :=
    fac3_mul hM0 hd0
  have eB : (s ^ 9 * (x ^ 3 * ((x + 2) * (x ^ 2 + 3 * x + 3)))).factorization 3 =
      (s ^ 9).factorization 3 + (x ^ 3 * ((x + 2) * (x ^ 2 + 3 * x + 3))).factorization 3 :=
    fac3_mul (pow_ne_zero 9 hs0) hFY0
  have eC : (s ^ 9).factorization 3 = 9 * s.factorization 3 := fac3_pow s 9
  have eD : (x ^ 3 * ((x + 2) * (x ^ 2 + 3 * x + 3))).factorization 3 =
      (x ^ 3).factorization 3 + ((x + 2) * (x ^ 2 + 3 * x + 3)).factorization 3 :=
    fac3_mul (pow_ne_zero 3 hx0) (mul_ne_zero hx20 hC0)
  have eE : (x ^ 3).factorization 3 = 3 * x.factorization 3 := fac3_pow x 3
  have eF : ((x + 2) * (x ^ 2 + 3 * x + 3)).factorization 3 =
      (x + 2).factorization 3 + (x ^ 2 + 3 * x + 3).factorization 3 :=
    fac3_mul hx20 hC0
  have hdiv := congrArg (fun n => n.factorization 3) E2'
  omega

theorem cross_p3_D {M s a d : ℕ} (hs2 : 2 ≤ s) (hs3 : ¬ 3 ∣ s) (hd : d ∣ 4) (hd1 : 1 ≤ d)
    (hfac : M.factorization 3 = 6 * a)
    (E2 : M * d = s ^ 12 * ((s ^ 4 - 1) * ((s ^ 2 - 1) * ((s ^ 4 - 1) * (s ^ 6 - 1))))) :
    False := by
  obtain ⟨x, hx⟩ : ∃ x, s ^ 2 = x + 1 :=
    ⟨s ^ 2 - 1, by have : 1 ≤ s ^ 2 := Nat.one_le_pow _ _ (by omega); omega⟩
  obtain ⟨hx2, hx4, hx6, -, -⟩ := sq_facts hx
  have h3x : 3 ∣ x := three_dvd_x hs3 hx
  obtain ⟨hn2, -, hC⟩ := three_dvd_facts h3x
  have hx1 : 1 ≤ x := by nlinarith
  have E2' : M * d = s ^ 12 * (x ^ 4 * ((x + 2) ^ 2 * (x ^ 2 + 3 * x + 3))) := by
    rw [E2, hx2, hx4, hx6]
    ring
  have hx0 : x ≠ 0 := by omega
  have hC0 : x ^ 2 + 3 * x + 3 ≠ 0 := by omega
  have hx20 : x + 2 ≠ 0 := by omega
  have hFY0 : x ^ 4 * ((x + 2) ^ 2 * (x ^ 2 + 3 * x + 3)) ≠ 0 :=
    mul_ne_zero (pow_ne_zero 4 hx0) (mul_ne_zero (pow_ne_zero 2 hx20) hC0)
  have hM0 : M ≠ 0 := by
    rintro rfl
    rw [zero_mul] at E2'
    exact mul_ne_zero (pow_ne_zero 12 (by omega)) hFY0 E2'.symm
  have hd0 : d ≠ 0 := by omega
  have hs0 : s ≠ 0 := by omega
  have hsf : s.factorization 3 = 0 := Nat.factorization_eq_zero_of_not_dvd hs3
  have hdf : d.factorization 3 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd fun h => by
      have := h.trans hd
      norm_num at this
  have hxn2 : (x + 2).factorization 3 = 0 := Nat.factorization_eq_zero_of_not_dvd hn2
  have eA : (M * d).factorization 3 = M.factorization 3 + d.factorization 3 :=
    fac3_mul hM0 hd0
  have eB : (s ^ 12 * (x ^ 4 * ((x + 2) ^ 2 * (x ^ 2 + 3 * x + 3)))).factorization 3 =
      (s ^ 12).factorization 3 + (x ^ 4 * ((x + 2) ^ 2 * (x ^ 2 + 3 * x + 3))).factorization 3 :=
    fac3_mul (pow_ne_zero 12 hs0) hFY0
  have eC : (s ^ 12).factorization 3 = 12 * s.factorization 3 := fac3_pow s 12
  have eD : (x ^ 4 * ((x + 2) ^ 2 * (x ^ 2 + 3 * x + 3))).factorization 3 =
      (x ^ 4).factorization 3 + ((x + 2) ^ 2 * (x ^ 2 + 3 * x + 3)).factorization 3 :=
    fac3_mul (pow_ne_zero 4 hx0) (mul_ne_zero (pow_ne_zero 2 hx20) hC0)
  have eE : (x ^ 4).factorization 3 = 4 * x.factorization 3 := fac3_pow x 4
  have eF : ((x + 2) ^ 2 * (x ^ 2 + 3 * x + 3)).factorization 3 =
      ((x + 2) ^ 2).factorization 3 + (x ^ 2 + 3 * x + 3).factorization 3 :=
    fac3_mul (pow_ne_zero 2 hx20) hC0
  have eG : ((x + 2) ^ 2).factorization 3 = 2 * (x + 2).factorization 3 := fac3_pow (x + 2) 2
  have hdiv := congrArg (fun n => n.factorization 3) E2'
  omega

theorem cross_p3_D2 {M s a d : ℕ} (hs2 : 2 ≤ s) (hs3 : ¬ 3 ∣ s) (hd : d ∣ 4) (hd1 : 1 ≤ d)
    (hfac : M.factorization 3 = 6 * a)
    (E2 : M * d = s ^ 12 * ((s ^ 4 + 1) * ((s ^ 2 - 1) * ((s ^ 4 - 1) * (s ^ 6 - 1))))) :
    False := by
  obtain ⟨x, hx⟩ : ∃ x, s ^ 2 = x + 1 :=
    ⟨s ^ 2 - 1, by have : 1 ≤ s ^ 2 := Nat.one_le_pow _ _ (by omega); omega⟩
  obtain ⟨hx2, hx4, hx6, hx41, -⟩ := sq_facts hx
  have h3x : 3 ∣ x := three_dvd_x hs3 hx
  obtain ⟨hn2, hn4, hC⟩ := three_dvd_facts h3x
  have hx1 : 1 ≤ x := by nlinarith
  have E2' : M * d = s ^ 12 * ((x * (x + 2) + 2) * (x ^ 3 * ((x + 2) * (x ^ 2 + 3 * x + 3)))) := by
    rw [E2, hx41, hx2, hx4, hx6]
    ring
  have hx0 : x ≠ 0 := by omega
  have hC0 : x ^ 2 + 3 * x + 3 ≠ 0 := by omega
  have hx20 : x + 2 ≠ 0 := by omega
  have hA0 : x * (x + 2) + 2 ≠ 0 := by omega
  have hFY0 : (x * (x + 2) + 2) * (x ^ 3 * ((x + 2) * (x ^ 2 + 3 * x + 3))) ≠ 0 :=
    mul_ne_zero hA0 (mul_ne_zero (pow_ne_zero 3 hx0) (mul_ne_zero hx20 hC0))
  have hM0 : M ≠ 0 := by
    rintro rfl
    rw [zero_mul] at E2'
    exact mul_ne_zero (pow_ne_zero 12 (by omega)) hFY0 E2'.symm
  have hd0 : d ≠ 0 := by omega
  have hs0 : s ≠ 0 := by omega
  have hsf : s.factorization 3 = 0 := Nat.factorization_eq_zero_of_not_dvd hs3
  have hdf : d.factorization 3 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd fun h => by
      have := h.trans hd
      norm_num at this
  have hA3 : (x * (x + 2) + 2).factorization 3 = 0 := Nat.factorization_eq_zero_of_not_dvd hn4
  have hxn2 : (x + 2).factorization 3 = 0 := Nat.factorization_eq_zero_of_not_dvd hn2
  have eA : (M * d).factorization 3 = M.factorization 3 + d.factorization 3 :=
    fac3_mul hM0 hd0
  have eB : (s ^ 12 * ((x * (x + 2) + 2) * (x ^ 3 * ((x + 2) * (x ^ 2 + 3 * x + 3))))).factorization 3 =
      (s ^ 12).factorization 3 +
        ((x * (x + 2) + 2) * (x ^ 3 * ((x + 2) * (x ^ 2 + 3 * x + 3)))).factorization 3 :=
    fac3_mul (pow_ne_zero 12 hs0) hFY0
  have eC : (s ^ 12).factorization 3 = 12 * s.factorization 3 := fac3_pow s 12
  have eD : ((x * (x + 2) + 2) * (x ^ 3 * ((x + 2) * (x ^ 2 + 3 * x + 3)))).factorization 3 =
      (x * (x + 2) + 2).factorization 3 +
        (x ^ 3 * ((x + 2) * (x ^ 2 + 3 * x + 3))).factorization 3 :=
    fac3_mul hA0 (mul_ne_zero (pow_ne_zero 3 hx0) (mul_ne_zero hx20 hC0))
  have eE : (x ^ 3 * ((x + 2) * (x ^ 2 + 3 * x + 3))).factorization 3 =
      (x ^ 3).factorization 3 + ((x + 2) * (x ^ 2 + 3 * x + 3)).factorization 3 :=
    fac3_mul (pow_ne_zero 3 hx0) (mul_ne_zero hx20 hC0)
  have eF : (x ^ 3).factorization 3 = 3 * x.factorization 3 := fac3_pow x 3
  have eG : ((x + 2) * (x ^ 2 + 3 * x + 3)).factorization 3 =
      (x + 2).factorization 3 + (x ^ 2 + 3 * x + 3).factorization 3 :=
    fac3_mul hx20 hC0
  have hdiv := congrArg (fun n => n.factorization 3) E2'
  omega

end CFSG.LocalAnalysis.GLTheoremA.SFM11
