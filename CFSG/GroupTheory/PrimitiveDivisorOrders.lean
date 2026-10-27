module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51eZsig

public section

namespace CFSG.GroupTheory

inductive GoodFactor (q M : ℕ) : ℕ → Prop
  | pow (E : ℕ) : GoodFactor q M (q ^ E)
  | sub (i : ℕ) (hi : 0 < i) (h : i < M) : GoodFactor q M (q ^ i - 1)
  | add (i : ℕ) (hi : 0 < i) (h : 2 * i < M) : GoodFactor q M (q ^ i + 1)
  | triality (a : ℕ) (ha : 0 < a) (h : 12 * a < M) :
      GoodFactor q M (q ^ (8 * a) + q ^ (4 * a) + 1)
  | mul {A B : ℕ} : GoodFactor q M A → GoodFactor q M B → GoodFactor q M (A * B)

lemma pow_three_mul_sub_one {q m : ℕ} (hq : 0 < q) :
    q ^ (3 * m) - 1 = (q ^ m - 1) * (q ^ (2 * m) + q ^ m + 1) := by
  have h2 : q ^ (2 * m) = (q ^ m) ^ 2 := by rw [mul_comm, pow_mul]
  rw [show q ^ (3 * m) = (q ^ m) ^ 3 by rw [show 3 * m = m * 3 by ring, pow_mul], h2]
  obtain ⟨x, hx⟩ : ∃ x, q ^ m = x + 1 :=
    ⟨q ^ m - 1, by have := Nat.one_le_pow m q hq; omega⟩
  rw [hx]
  have e : (x + 1) ^ 3 = x * ((x + 1) ^ 2 + (x + 1) + 1) + 1 := by ring
  rw [e, Nat.add_sub_cancel]
  simp

lemma factorization_of_mul_eq {M q A B e : ℕ} (hq : q.Prime)
    (h : M * A = q ^ e * B) (hA : ¬ q ∣ A) (hB : ¬ q ∣ B)
    (hA0 : 0 < A) (hB0 : 0 < B) (hM0 : 0 < M) : M.factorization q = e := by
  have hfac := congrArg (fun n => n.factorization q) h
  rw [Nat.factorization_mul hM0.ne' hA0.ne',
    Nat.factorization_mul (pow_ne_zero e hq.ne_zero) hB0.ne'] at hfac
  simp only [Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hA,
    Nat.factorization_eq_zero_of_not_dvd hB, hq.factorization_pow,
    Finsupp.single_eq_same, add_zero] at hfac
  exact hfac

lemma gcd_two_pow_sub_one {q n : ℕ} (hq : Odd q) (hn : 0 < n) : Nat.gcd 2 (q ^ n - 1) = 2 := by
  have hqodd : Odd (q ^ n) := hq.pow
  have h2 : 2 ∣ q ^ n - 1 := by
    obtain ⟨k, hk⟩ := hqodd
    rw [show q ^ n - 1 = 2 * k by omega]
    exact dvd_mul_right 2 k
  rw [Nat.gcd_comm]
  exact Nat.gcd_eq_right h2

lemma cross_mul_eq_of_mul_eq {M N1 N2 d1 d2 : ℕ} (h1 : M * d1 = N1) (h2 : M * d2 = N2) :
    d2 * N1 = d1 * N2 := by
  calc d2 * N1 = d2 * (M * d1) := by rw [h1]
    _ = (M * d2) * d1 := by ring
    _ = N2 * d1 := by rw [h2]
    _ = d1 * N2 := by ring

end CFSG.GroupTheory

namespace CFSG.ComponentClassification.HarrisLit.T1.P51e

namespace IsPrimDiv

theorem not_dvd_of_goodFactor {ℓ q M F : ℕ} (h : IsPrimDiv ℓ q M) (hq : 0 < q)
    (hM : 0 < M) (hg : CFSG.GroupTheory.GoodFactor q M F) : ¬ ℓ ∣ F := by
  induction hg with
  | pow E =>
      by_cases hE : E = 0
      · subst hE
        rw [pow_zero]
        exact fun hd => h.1.ne_one (Nat.dvd_one.mp hd)
      · exact fun hd => h.not_dvd_base hq hM (h.1.dvd_of_dvd_pow hd)
  | sub i hi hlt =>
      exact fun hd => h.2.2 i hi hlt hd
  | add i hi h2i =>
      intro hd
      have hfac : q ^ (2 * i) - 1 = (q ^ i - 1) * (q ^ i + 1) :=
        CFSG.ComponentClassification.HarrisLit.T1.P51e.pow_two_mul_sub_one q i
      have hd2 : ℓ ∣ q ^ (2 * i) - 1 := by
        rw [hfac]
        exact dvd_mul_of_dvd_right hd _
      exact h.2.2 (2 * i) (by omega) h2i hd2
  | triality a ha h12a =>
      intro hd
      have hfac : q ^ (12 * a) - 1 =
          (q ^ (4 * a) - 1) * (q ^ (8 * a) + q ^ (4 * a) + 1) := by
        have hx1 : 1 ≤ q ^ (4 * a) := Nat.one_le_pow _ _ hq
        obtain ⟨x, hx⟩ : ∃ x, q ^ (4 * a) = x + 1 := ⟨q ^ (4 * a) - 1, by omega⟩
        have h12 : q ^ (12 * a) = (x + 1) ^ 3 := by
          rw [← hx, show 12 * a = 4 * a * 3 by ring, pow_mul]
        have h8 : q ^ (8 * a) = (x + 1) ^ 2 := by
          rw [← hx, show 8 * a = 4 * a * 2 by ring, pow_mul]
        rw [h12, h8, hx]
        have e : (x + 1) ^ 3 = x * ((x + 1) ^ 2 + (x + 1) + 1) + 1 := by ring
        rw [e, Nat.add_sub_cancel]
        simp
      have hd2 : ℓ ∣ q ^ (12 * a) - 1 := by
        rw [hfac]
        exact dvd_mul_of_dvd_right hd _
      exact h.2.2 (12 * a) (by omega) h12a hd2
  | mul hA hB ihA ihB =>
      exact fun hd => (h.1.dvd_mul.mp hd).elim ihA ihB

theorem no_order_eq_of_primitive_divisor {M NX NY dX dY ℓ q m : ℕ}
    (hX : M * dX = NX) (hY : M * dY = NY) (hr : IsPrimDiv ℓ q m) (hrNX : ℓ ∣ NX)
    (hrdX : ¬ ℓ ∣ dX) (hq : 0 < q) (hm : 0 < m)
    (hg : CFSG.GroupTheory.GoodFactor q m NY) : False := by
  have hrM : ℓ ∣ M := by
    have h : ℓ ∣ M * dX := by rw [hX]; exact hrNX
    exact (hr.1.dvd_mul.mp h).resolve_right hrdX
  have hrNY : ℓ ∣ NY := by
    rw [← hY, mul_comm]
    exact dvd_mul_of_dvd_right hrM dY
  exact hr.not_dvd_of_goodFactor hq hm hg hrNY

end IsPrimDiv

end CFSG.ComponentClassification.HarrisLit.T1.P51e

end
