module

public import CFSG.GH74.Uniqueness.Section128Arith
public import CFSG.GH74.Uniqueness.Section128Count

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

namespace Sec1210

theorem cases_u (h123 : Lemma123Stmt Z M) (h124 : Lemma124Stmt Z M)
    (h128 : Lemma128Stmt Z M) (h129 : Lemma129Stmt Z M) {c : Ctx12 Z M} {n i : ℕ}
    (h : LData c n i) {u : X} (huD : u ∈ c.D) (hu2 : orderOf u = 2) :
    (cenHull Z u = c.L ∧
      (omega M).ncard = ((2 ^ n) ^ i + 1) * ((2 ^ n) ^ i * (2 ^ n - 1) + 1) ∧
      (omegaFix M ({u} : Set X)).ncard = (2 ^ n) ^ i + 1) ∨
    (i = 1 ∧ c.L < cenHull Z u ∧ (∃ e, BenderSub Z M (cenHull Z u) n 3 e) ∧
      (omega M).ncard = ((2 ^ n) ^ 3 + 1) * ((2 ^ n) ^ 3 * (2 ^ n - 1) + 1) ∧
      (omegaFix M ({u} : Set X)).ncard = (2 ^ n) ^ 3 + 1) := by
  obtain ⟨hcM, hLu⟩ := h129 c n i h u huD hu2
  have hcent : u ∈ centralizer (zHull Z M : Set X) :=
    mem_centralizer_iff.mpr fun x hx => (hcM x hx).symm
  obtain ⟨-, -, ⟨m, j, e, -, hq, hB⟩, -, -⟩ := h124 c n i h u huD hu2
  obtain ⟨hΩu, hcase⟩ := h128 c n i h u huD hu2 m j e hB hq
  obtain ⟨hmn, hΩ⟩ : m = n ∧ (omega M).ncard =
      ((2 ^ m) ^ j + 1) * ((2 ^ m) ^ j * (2 ^ m - 1) + 1) := by
    rcases hcase with ⟨-, h1, h2⟩ | ⟨h2, -, -⟩
    · exact ⟨h1, h2⟩
    · exact absurd hcent h2
  subst hmn
  have hvL : u ∈ centralizer (c.L : Set X) := mem_centralizer_iff.mpr fun y hy =>
    mem_centralizer_singleton_iff.mp (Cor713.zHull_le _ (hLu hy))
  rcases h123 c _ i h u hvL (Sec128.ne_one_of_two hu2) with heq | ⟨hi1, hlt, e', hB'⟩
  · left
    have hji : j = i := by
      have hB2 : BenderSub Z M c.L m j e := heq ▸ hB
      have hT : Bender.BenderType (↥c.L ⧸ center ↥c.L) m i 1 :=
        h.bender.of_mulEquiv (centerBotEquiv h.center_eq_bot)
      exact (hB2.bender.unique hT).2.1
    subst hji
    exact ⟨heq, hΩ, hΩu⟩
  · right
    have hj3 : j = 3 := (hB.bender.unique hB'.bender).2.1
    subst hj3
    exact ⟨hi1, hlt, ⟨e', hB'⟩, hΩ, hΩu⟩

end Sec1210

theorem ZDSetup.lemma1210
    (S : ZDSetup X Z M) (h123 : Lemma123Stmt Z M) (h124 : Lemma124Stmt Z M)
    (h128 : Lemma128Stmt Z M) (h129 : Lemma129Stmt Z M) : Lemma1210Stmt Z M := by
  intro c n i h
  have hcases := fun {u : X} (huD : u ∈ c.D) (hu2 : orderOf u = 2) =>
    Sec1210.cases_u h123 h124 h128 h129 h huD hu2
  obtain ⟨u₀, hu₀⟩ := exists_prime_orderOf_dvd_card' (G := ↥c.D) 2 (even_iff_two_dvd.mp c.hD)
  have hu₀2 : orderOf (u₀ : X) = 2 := by rw [Subgroup.orderOf_coe]; exact hu₀
  have hq2 : 2 ≤ 2 ^ n := Nat.one_lt_two_pow (by have := h.hn; omega)
  have hn1 : 1 ≤ n := by have := h.hn; omega
  have hqe : Even (2 ^ n) := (Nat.even_pow' (by omega)).mpr even_two
  have hvals := Sec128.arith_values (2 ^ n) (by omega)
  have hX : Nat.card X = (omega M).ncard * (((omega M).ncard - 1) * Nat.card ↥c.D) := by
    rw [S.ncard_omega_sub_one_mul_card c.htM, S.prodDisc.ncard_omega_mul_card]
  have hD0 : 0 < Nat.card ↥c.D := Nat.card_pos
  have h3 : (2 : ℕ) ^ (3 * n) = (2 ^ n) ^ 3 := by rw [← pow_mul, mul_comm]
  have h4 : (2 : ℕ) ^ (4 * n) = (2 ^ n) ^ 4 := by rw [← pow_mul, mul_comm]
  have hL := h.bender.card_eq
  rcases hcases u₀.2 hu₀2 with ⟨-, hΩ₀, -⟩ | ⟨hi1, -, -, hΩ₀, -⟩
  · rcases h.hi with rfl | rfl
    ·
      left
      have hΩ : (omega M).ncard = (2 ^ n) ^ 3 + 1 := hΩ₀.trans hvals.1
      refine ⟨rfl, hΩ, fun u huD hu2 => ?_, ?_⟩
      · rcases hcases huD hu2 with ⟨heq, -, hΩu⟩ | ⟨-, -, -, hΩc, -⟩
        · refine ⟨heq, by rw [hΩu, pow_one], ?_⟩
          rw [hL, hΩu, hΩ₀]
          exact hvals.2.2.2.1
        · exact (Sec128.arith_ne hq2 hΩ (by rw [hΩc]; exact hvals.2.2.1)).elim
      · rw [hX]
        refine Sec128.factorization_card (r := 1) (by omega) odd_one ?_ hD0
        rw [hΩ, mul_one, h3]
    ·
      right; left
      refine ⟨rfl, by rw [hΩ₀]; exact hvals.2.1, fun u huD hu2 => ?_, ?_⟩
      · rcases hcases huD hu2 with ⟨heq, -, hΩu⟩ | ⟨h21, -, -, -, -⟩
        · refine ⟨heq, hΩu, ?_⟩
          rw [hL, hΩu, hΩ₀]
          exact hvals.2.2.2.2
        · exact absurd h21 (by norm_num)
      · rw [hX]
        refine Sec128.factorization_card (r := 2 ^ n * (2 ^ n - 1) + 1) (by omega)
          (Sec128.odd_mul_add_one hqe _) ?_ hD0
        rw [hΩ₀, Sec128.arith_omega_b _ (by omega), h3]
  ·
    right; right
    refine ⟨hi1, by rw [hΩ₀]; exact hvals.2.2.1, fun u huD hu2 => ?_, ?_⟩
    · rcases hcases huD hu2 with ⟨-, hΩa, -⟩ | ⟨-, hlt, hB, -, hΩu⟩
      · exfalso
        rw [hi1] at hΩa
        exact Sec128.arith_ne hq2 (hΩa.trans hvals.1) (by rw [hΩ₀]; exact hvals.2.2.1)
      · exact ⟨hlt, hB, hΩu⟩
    · rw [hX]
      refine Sec128.factorization_card (r := (2 ^ n) ^ 2 * (2 ^ n - 1) + 1) (by omega)
        (Sec128.odd_mul_add_one (Nat.even_pow.mpr ⟨hqe, two_ne_zero⟩) _) ?_ hD0
      rw [hΩ₀, Sec128.arith_omega_c _ (by omega), h4]

end CFSG.GH74.Uniqueness
