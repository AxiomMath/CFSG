module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherSubspaceIndex

public section

namespace CFSG.CGT.T75N

open Matrix Module CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped Pointwise

section Index

variable {K : Type} [Field K] [Finite K] {n : ℕ}

omit [Finite K] in
theorem index_stabilizer_eq_card {k : ℕ} (W : Submodule K (Fin n → K)) (hW : finrank K W = k) :
    (stabilizer W).index = Nat.card {W' : Submodule K (Fin n → K) // finrank K W' = k} := by
  rw [stabilizer_eq_mulAction_stabilizer, MulAction.index_stabilizer, ← Nat.card_coe_set_eq]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun W' => ?_)
  rw [MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨g, rfl⟩
    rw [smul_submodule_eq_map, ← hW]
    exact LinearEquiv.finrank_map_eq (Matrix.SpecialLinearGroup.toLin' g) W
  · intro h
    obtain ⟨g, hg⟩ := exists_map_eq_of_finrank_eq (h.trans hW.symm).symm
    exact ⟨g, hg⟩

theorem index_stabilizer_gauss {k : ℕ} (hk : k ≤ n) (W : Submodule K (Fin n → K))
    (hW : finrank K W = k) :
    ((stabilizer W).index : ℚ) = gaussianCoeff n k (Nat.card K) := by
  rw [index_stabilizer_eq_card W hW]
  exact card_finrank_eq hk

theorem index_stabilizer_flag_gauss {k : ℕ} (hk : k ≤ n) :
    ((stabilizer (flagSpace n K k)).index : ℚ) = gaussianCoeff n k (Nat.card K) :=
  index_stabilizer_gauss hk _ (finrank_flagSpace hk)

theorem index_stabilizer_flag_one (hn : 1 ≤ n) :
    ((stabilizer (flagSpace n K 1)).index) * (Nat.card K - 1) = Nat.card K ^ n - 1 := by
  have hq : 2 ≤ Nat.card K := by
    have := Finite.one_lt_card (α := K)
    omega
  have h := index_stabilizer_flag_gauss (K := K) hn
  rw [gaussianCoeff_one] at h
  have hq1 : ((Nat.card K : ℚ) - 1) ≠ 0 := by
    have : (2 : ℚ) ≤ Nat.card K := by exact_mod_cast hq
    linarith
  have h2 : ((stabilizer (flagSpace n K 1)).index : ℚ) * ((Nat.card K : ℚ) - 1) =
      (Nat.card K : ℚ) ^ n - 1 := by
    rw [h]
    field_simp
  have h3 : 1 ≤ Nat.card K ^ n := Nat.one_le_pow _ _ (by omega)
  have h4 : ((((stabilizer (flagSpace n K 1)).index) * (Nat.card K - 1) : ℕ) : ℚ) =
      ((Nat.card K ^ n - 1 : ℕ) : ℚ) := by
    push_cast [Nat.cast_sub (by omega : 1 ≤ Nat.card K), Nat.cast_sub h3]
    exact h2
  exact_mod_cast h4

end Index

section Gauss

variable {q n : ℕ}

theorem gaussianCoeff_add_one_le (hq : 2 ≤ q) (hn : 2 ≤ n) {k : ℕ} (hk1 : 1 ≤ k) (hkn : k < n) :
    (q : ℚ) + 1 ≤ gaussianCoeff n k q := by
  have hq' : (2 : ℚ) ≤ q := by exact_mod_cast hq
  have hq1 : (0 : ℚ) < (q : ℚ) - 1 := by linarith
  have hone : (q : ℚ) + 1 ≤ gaussianCoeff n 1 q := by
    rw [gaussianCoeff_one, le_div_iff₀ hq1]
    have : (q : ℚ) ^ 2 ≤ (q : ℚ) ^ n := pow_le_pow_right₀ (by linarith) hn
    nlinarith
  rcases Nat.lt_or_ge n 3 with hn3 | hn3
  · obtain rfl : n = 2 := by omega
    obtain rfl : k = 1 := by omega
    exact hone
  · exact hone.trans (gaussian_minimum hq hn3 hk1 hkn).2.1

theorem gaussianCoeff_two_le (hq : 2 ≤ q) {n : ℕ} :
    ∀ k, 2 ≤ k → 2 * k ≤ n → gaussianCoeff n 2 q ≤ gaussianCoeff n k q := by
  intro k
  induction k with
  | zero => intro h; omega
  | succ k ih =>
    intro hk hkn
    rcases Nat.lt_or_ge k 2 with hk2 | hk2
    · obtain rfl : k = 1 := by omega
      exact le_rfl
    · exact (ih hk2 (by omega)).trans (gaussianCoeff_lt_succ hq (by omega)).le

theorem gaussianCoeff_two_gt (hq : 2 ≤ q) (hn : 4 ≤ n) :
    (q : ℚ) ^ n - 1 < gaussianCoeff n 2 q := by
  have hq' : (2 : ℚ) ≤ q := by exact_mod_cast hq
  have hq1 : (0 : ℚ) < (q : ℚ) - 1 := by linarith
  have hq2 : (0 : ℚ) < (q : ℚ) ^ 2 - 1 := by nlinarith
  have h1 := gaussianCoeff_succ hq (n := n) (k := 1) (by omega)
  rw [gaussianCoeff_one] at h1
  have h2 : gaussianCoeff n 2 q = ((q : ℚ) ^ n - 1) / ((q : ℚ) - 1) *
      (((q : ℚ) ^ (n - 1) - 1) / ((q : ℚ) ^ 2 - 1)) := by
    simpa using h1
  rw [h2, div_mul_div_comm, lt_div_iff₀ (mul_pos hq1 hq2)]
  have hpos : (0 : ℚ) < (q : ℚ) ^ n - 1 := by
    have : (q : ℚ) ^ 1 < (q : ℚ) ^ n := pow_lt_pow_right₀ (by linarith) (by omega)
    linarith
  have h3 : (q : ℚ) ^ 3 ≤ (q : ℚ) ^ (n - 1) := pow_le_pow_right₀ (by linarith) (by omega)
  have h4 : ((q : ℚ) - 1) * ((q : ℚ) ^ 2 - 1) < (q : ℚ) ^ (n - 1) - 1 := by nlinarith
  nlinarith

theorem gaussianCoeff_gt (hq : 2 ≤ q) (hn : 4 ≤ n) {k : ℕ} (hk2 : 2 ≤ k) (hkn : k + 2 ≤ n) :
    (q : ℚ) ^ n - 1 < gaussianCoeff n k q := by
  refine (gaussianCoeff_two_gt hq hn).trans_le ?_
  rcases le_or_gt (2 * k) n with h | h
  · exact gaussianCoeff_two_le hq k hk2 h
  · rw [gaussianCoeff_symm hq (by omega : k ≤ n)]
    exact gaussianCoeff_two_le hq (n - k) (by omega) (by omega)

end Gauss

end CFSG.CGT.T75N
