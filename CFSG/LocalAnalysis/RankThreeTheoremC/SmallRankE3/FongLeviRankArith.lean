module

public import CFSG.LocalAnalysis.SectionRank.OddCover.ScalarCover

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLevi

open Subgroup CFSG.Open

theorem two_pow_two_mul_add_one_mod_three (j : ℕ) : 2 ^ (2 * j + 1) % 3 = 2 := by
  induction j with
  | zero => norm_num
  | succ j ih =>
    have e : 2 ^ (2 * (j + 1) + 1) = 2 ^ (2 * j + 1) * 4 := by ring
    rw [e, Nat.mul_mod, ih] <;> norm_num

theorem two_pow_two_mul_add_one_mod_five (j : ℕ) :
    2 ^ (2 * j + 1) % 5 = 2 ∨ 2 ^ (2 * j + 1) % 5 = 3 := by
  induction j with
  | zero => norm_num
  | succ j ih =>
    have e : 2 ^ (2 * (j + 1) + 1) = 2 ^ (2 * j + 1) * 4 := by ring
    rw [e, Nat.mul_mod]
    rcases ih with h | h <;> rw [h] <;> norm_num

theorem exists_prime_dvd_two_pow_sub_one_ne_five {f : ℕ} (hf : Odd f) (hf3 : 3 ≤ f) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ≠ 2 ∧ ℓ ≠ 5 ∧ ℓ ∣ 2 ^ f - 1 := by
  obtain ⟨k, rfl⟩ := hf
  have h8 : (8 : ℕ) ≤ 2 ^ (2 * k + 1) := by
    calc (8 : ℕ) = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (2 * k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨ℓ, hℓ, hℓd⟩ := Nat.exists_prime_and_dvd (show 2 ^ (2 * k + 1) - 1 ≠ 1 by omega)
  refine ⟨ℓ, hℓ, ?_, ?_, hℓd⟩
  · rintro rfl
    have h2 : 2 ∣ 2 ^ (2 * k + 1) := dvd_pow_self 2 (by omega)
    omega
  · rintro rfl
    have hmod := two_pow_two_mul_add_one_mod_five k
    omega

theorem three_dvd_two_pow_add_one {f : ℕ} (hf : Odd f) : 3 ∣ 2 ^ f + 1 := by
  obtain ⟨k, hk⟩ := hf
  obtain rfl : f = 2 * k + 1 := hk
  have h := two_pow_two_mul_add_one_mod_three k
  omega

theorem exists_prime_dvd_two_pow_add_one_ne_five {f : ℕ} (hf : Even f) (hf4 : 4 ≤ f) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ≠ 2 ∧ ℓ ≠ 5 ∧ ℓ ∣ 2 ^ f + 1 := by
  by_contra hne
  have hall : ∀ {d : ℕ}, d.Prime → d ∣ 2 ^ f + 1 → d = 5 := by
    intro d hd hdn
    by_contra h5
    have hd2 : d ≠ 2 := by
      rintro rfl
      have h2 : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
      omega
    exact hne ⟨d, hd, hd2, h5, hdn⟩
  have hpow := Nat.eq_prime_pow_of_unique_prime_dvd (by positivity : 2 ^ f + 1 ≠ 0) hall
  obtain ⟨a, ha⟩ : ∃ a, 2 ^ f + 1 = 5 ^ a := ⟨_, hpow⟩
  have h8 : 2 ^ f % 8 = 0 := by
    obtain ⟨m, hm⟩ : ∃ m, f = m + 3 := ⟨f - 3, by omega⟩
    rw [hm, pow_add, Nat.mul_mod] <;> norm_num
  have h3 : 2 ^ f % 3 = 1 := by
    obtain ⟨m, hm⟩ := hf
    rw [hm, ← two_mul, pow_mul, Nat.pow_mod] <;> norm_num
  rcases Nat.even_or_odd a with ⟨b, hb⟩ | ⟨b, hb⟩
  ·
    have h5 : 5 ^ a = 25 ^ b := by
      rw [hb, ← two_mul, pow_mul] <;> norm_num
    have h25 : 25 ^ b % 3 = 1 := by
      rw [Nat.pow_mod] <;> norm_num
    omega
  ·
    have h5 : 5 ^ a % 8 = 5 := by
      rw [hb, pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod] <;> norm_num
    omega

theorem scalar_pow_five_eq_one_of_le {K : Type} [Field K]
    {M : Subgroup (Matrix.GeneralLinearGroup (Fin 5) K)}
    (hM : M ≤ CFSG.Open.StatedSL 5 K) (c : Kˣ)
    (hc : Matrix.GeneralLinearGroup.scalar (Fin 5) c ∈ M) : c ^ 5 = 1 := by
  have hdet := CFSG.Open.StatedAPI.det_of_mem_statedSL (hM hc)
  rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hdet
  exact Units.ext (by simpa using hdet)

theorem psl_four_le_pRank_of_dvd {F : Type} [Field F] [Finite F] {n f ℓ : ℕ} [Fact ℓ.Prime]
    (hℓ2 : ℓ ≠ 2) (hn : 5 ≤ n) (hn5 : ℓ ≠ 5 ∨ 6 ≤ n) (hF : Nat.card F = 2 ^ f)
    (hℓ : ℓ ∣ 2 ^ f - 1) :
    4 ≤ CFSG.Open.pRank ℓ (⊤ : Subgroup (CFSG.Open.StatedProj (CFSG.Open.StatedSL n F))) := by
  have hrk := CFSG.SectionRank.OddCover.scalar_quotient_diagonal_torus_rank (K := F) (p := 2)
    (f := f) (n := n) (r := ℓ) (H := CFSG.Open.StatedSL n F) Nat.prime_two (by omega) hℓ2
    (Or.inl ⟨hF, rfl, hℓ⟩)
    ((CFSG.Open.StatedScalars (Fin n) F).subgroupOf (CFSG.Open.StatedSL n F)) le_rfl
  obtain ⟨h1, h2⟩ := hrk
  rcases Nat.lt_or_ge n 6 with hn6 | hn6
  ·
    obtain rfl : n = 5 := by omega
    have hℓ5 : ℓ ≠ 5 := by
      rcases hn5 with h | h
      · exact h
      · omega
    have hℓp : ℓ.Prime := Fact.out
    have hnd : ¬ ℓ ∣ 5 := fun h => hℓ5 ((Nat.prime_dvd_prime_iff_eq hℓp (by norm_num)).1 h)
    exact le_trans (by norm_num) (h2 (CFSG.Open.StatedAPI.not_dvd_card_statedScalars_subgroupOf
      (CFSG.Open.StatedSL 5 F) Fact.out hnd
      (fun c hc => scalar_pow_five_eq_one_of_le (le_refl (CFSG.Open.StatedSL 5 F)) c hc)))
  · exact le_trans (by omega) h1

theorem psu_four_le_pRank_of_dvd {F : Type} [Field F] [Finite F] {n f ℓ : ℕ} [Fact ℓ.Prime]
    (hℓ2 : ℓ ≠ 2) (hn : 5 ≤ n) (hn5 : ℓ ≠ 5 ∨ 6 ≤ n) (hF : Nat.card F = (2 ^ f) ^ 2)
    (hℓ : ℓ ∣ 2 ^ f + 1) :
    4 ≤ CFSG.Open.pRank ℓ
      (⊤ : Subgroup (CFSG.Open.StatedProj (CFSG.Open.StatedSU n (2 ^ f) F))) := by
  have hrk := CFSG.SectionRank.OddCover.scalar_quotient_diagonal_torus_rank (K := F) (p := 2)
    (f := f) (n := n) (r := ℓ) (H := CFSG.Open.StatedSU n (2 ^ f) F) Nat.prime_two (by omega) hℓ2
    (Or.inr ⟨hF, rfl, hℓ⟩)
    ((CFSG.Open.StatedScalars (Fin n) F).subgroupOf (CFSG.Open.StatedSU n (2 ^ f) F)) le_rfl
  obtain ⟨h1, h2⟩ := hrk
  rcases Nat.lt_or_ge n 6 with hn6 | hn6
  ·
    obtain rfl : n = 5 := by omega
    have hℓ5 : ℓ ≠ 5 := by
      rcases hn5 with h | h
      · exact h
      · omega
    have hℓp : ℓ.Prime := Fact.out
    have hnd : ¬ ℓ ∣ 5 := fun h => hℓ5 ((Nat.prime_dvd_prime_iff_eq hℓp (by norm_num)).1 h)
    exact le_trans (by norm_num) (h2 (CFSG.Open.StatedAPI.not_dvd_card_statedScalars_subgroupOf
      (CFSG.Open.StatedSU 5 (2 ^ f) F) Fact.out hnd
      (fun c hc => scalar_pow_five_eq_one_of_le
        (CFSG.Open.StatedAPI.statedSU_le_statedSL 5 (2 ^ f) F) c hc)))
  · exact le_trans (by omega) h1

theorem psu_sub_two_le_pRank_of_dvd {F : Type} [Field F] [Finite F] {n f ℓ : ℕ} [Fact ℓ.Prime]
    (hℓ2 : ℓ ≠ 2) (hn : 2 ≤ n) (hF : Nat.card F = (2 ^ f) ^ 2) (hℓ : ℓ ∣ 2 ^ f + 1) :
    n - 2 ≤ CFSG.Open.pRank ℓ
      (⊤ : Subgroup (CFSG.Open.StatedProj (CFSG.Open.StatedSU n (2 ^ f) F))) := by
  have hrk := CFSG.SectionRank.OddCover.scalar_quotient_diagonal_torus_rank (K := F) (p := 2)
    (f := f) (n := n) (r := ℓ) (H := CFSG.Open.StatedSU n (2 ^ f) F) Nat.prime_two hn hℓ2
    (Or.inr ⟨hF, rfl, hℓ⟩)
    ((CFSG.Open.StatedScalars (Fin n) F).subgroupOf (CFSG.Open.StatedSU n (2 ^ f) F)) le_rfl
  exact hrk.1

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLevi
