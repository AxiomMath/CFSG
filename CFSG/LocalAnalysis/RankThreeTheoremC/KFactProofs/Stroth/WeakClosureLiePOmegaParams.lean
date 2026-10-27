module

public import CFSG.GroupTheory.WeirSylow.Orthogonal

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure

open CFSG.GroupTheory.WeirSylow Module QuadraticMap

theorem odd_dim_params {K : Type} [Field K] [Fintype K] {p : ℕ} [hp : Fact p.Prime]
    (hp1 : Odd p) (hpK : ¬ p ∣ Fintype.card K) {V : Type} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {n : ℕ} (h2 : ringChar K ≠ 2) (hdim : finrank K V = 2 * n + 1)
    {Q : QuadraticForm K V} (hQ : (polarBilin Q).Nondegenerate) :
    (Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q)).factorization p =
      weirA p K * ((if Even (weirE p K) then 2 * n else n) / weirE p K) +
        padicValNat p ((if Even (weirE p K) then 2 * n else n) / weirE p K).factorial := by
  have hpK' : ¬ p ∣ Nat.card K := by rwa [Nat.card_eq_fintype_card]
  rw [factorization_card_orthogonalGroup_odd hp1 hpK' h2 hQ hdim,
    factorization_card_statedSp hp1 K hpK n]

theorem even_dim_params {K : Type} [Field K] [Fintype K] {p : ℕ} [hp : Fact p.Prime]
    (hp1 : Odd p) (hpK : ¬ p ∣ Fintype.card K) {V : Type} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {n : ℕ} (hn : 4 ≤ n) (hdim : finrank K V = 2 * n)
    {Q : QuadraticForm K V} (hQ : (polarBilin Q).Nondegenerate) {ε : ℤ}
    (hε : (ε = 1 ∧ IsPlusType Q) ∨ (ε = -1 ∧ ¬ IsPlusType Q)) :
    ∃ k : ℕ, 3 ≤ k ∧ k ≤ n ∧
      (Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q)).factorization p =
        weirA p K * ((if Even (weirE p K) then 2 * k else k) / weirE p K) +
          padicValNat p ((if Even (weirE p K) then 2 * k else k) / weirE p K).factorial ∧
      (¬ Even (weirE p K) → weirE p K * (k / weirE p K) = n → IsPlusType Q) ∧
      (∀ f : ℕ, weirE p K = 2 * f → f * (k / f) = n → (IsPlusType Q ↔ Even (k / f))) := by
  have hn1 : 1 ≤ n := by omega
  have hεpm : ε = 1 ∨ ε = -1 := by rcases hε with ⟨h, -⟩ | ⟨h, -⟩ <;> simp [h]
  have hpK' : ¬ p ∣ Nat.card K := by rwa [Nat.card_eq_fintype_card]
  obtain ⟨hfac1, hfac2⟩ := factorization_card_orthogonalGroup_even hp1 hpK' hQ hn1 hdim hε
  rw [Nat.card_eq_fintype_card] at hfac1 hfac2
  have hdisj : ¬ (p : ℤ) ∣ (Fintype.card K : ℤ) ^ n + ε ∨
      ¬ (p : ℤ) ∣ (Fintype.card K : ℤ) ^ n - ε := by
    rcases hεpm with rfl | rfl
    · exact not_dvd_add_one_or_not_dvd_sub_one hp1 _
    · rw [← sub_eq_add_neg, sub_neg_eq_add]
      exact (not_dvd_add_one_or_not_dvd_sub_one hp1 _).symm
  rcases hdisj with h | h
  ·
    refine ⟨n, by omega, le_rfl, ?_, ?_, ?_⟩
    · rw [hfac1 h, factorization_card_statedSp hp1 K hpK n]
    · intro _ hen
      have hd : (p : ℤ) ∣ (Fintype.card K : ℤ) ^ n - 1 :=
        (dvd_pow_sub_one_iff_weirE n).2 ⟨n / weirE p K, hen.symm⟩
      rcases hε with ⟨rfl, hpl⟩ | ⟨rfl, -⟩
      · exact hpl
      · exact absurd (by rw [← sub_eq_add_neg]; exact hd) h
    · intro f hf hfn
      have hcong := dvd_pow_mul_sub_neg_one_pow hpK (f := f) hf (n / f)
      rw [hfn] at hcong
      have hεm : ε = (-1) ^ (n / f) := by
        by_contra hne
        apply h
        have hε'' : ε = -(-1) ^ (n / f) := by
          rcases neg_one_pow_eq_or ℤ (n / f) with h' | h' <;> rcases hεpm with rfl | rfl <;>
            simp_all
        rw [hε'', ← sub_eq_add_neg]
        exact hcong
      rcases hε with ⟨rfl, hpl⟩ | ⟨rfl, hnp⟩
      · exact iff_of_true hpl ((neg_one_pow_eq_one_iff_even (by norm_num)).1 hεm.symm)
      · refine iff_of_false hnp fun hev => ?_
        rw [(neg_one_pow_eq_one_iff_even (by norm_num)).2 hev] at hεm
        norm_num at hεm
  ·
    refine ⟨n - 1, by omega, by omega, ?_, ?_, ?_⟩
    · rw [hfac2 h, factorization_card_statedSp hp1 K hpK (n - 1)]
    · intro _ hen
      have := Nat.mul_div_le (n - 1) (weirE p K)
      omega
    · intro f _ hfn
      have := Nat.mul_div_le (n - 1) f
      omega

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure
