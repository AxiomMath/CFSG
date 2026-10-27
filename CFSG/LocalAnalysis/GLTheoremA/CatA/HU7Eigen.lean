module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.HU7Key

public section

namespace CFSG.LocalAnalysis.GLTheoremA.HU7

open Matrix CFSG.LocalAnalysis.GLTheoremA.Y10GNegCore

variable {F : Type} [Field F] [CharP F 2]

@[expose] def Eig (B : Matrix (Fin 6) (Fin 6) F) (c : F) : Matrix (Fin 6) (Fin 6) F :=
  1 + (c ^ 2) • B + c • (B ^ 2)

theorem cube_pow_eq_one {ω : F} (hω3 : ω ^ 3 = 1) (j : ℕ) : (ω ^ j) ^ 3 = 1 := by
  rw [← pow_mul, mul_comm, pow_mul, hω3, one_pow]

theorem one_add_omega_add_sq {ω : F} (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) : 1 + ω + ω ^ 2 = 0 := by
  have h : (ω - 1) * (1 + ω + ω ^ 2) = 0 := by linear_combination hω3
  rcases mul_eq_zero.1 h with h1 | h1
  · exact absurd (sub_eq_zero.1 h1) hω1
  · exact h1

theorem pow_ne_one_of_mod {ω : F} (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) (k : ℕ) (hk : k % 3 ≠ 0) :
    ω ^ k ≠ 1 := by
  have hk' : ω ^ k = ω ^ (k % 3) := by
    conv_lhs => rw [← Nat.div_add_mod k 3, pow_add, pow_mul, hω3, one_pow, one_mul]
  rw [hk']
  rcases (by omega : k % 3 = 1 ∨ k % 3 = 2) with h | h
  · rw [h, pow_one]
    exact hω1
  · rw [h]
    intro h2
    have h4 : ω ^ 4 = ω := by linear_combination ω * hω3
    have h4' : ω ^ 4 = 1 := by rw [show ω ^ 4 = (ω ^ 2) ^ 2 by ring, h2, one_pow]
    exact hω1 (h4.symm.trans h4')

theorem B_mul_Eig {B : Matrix (Fin 6) (Fin 6) F} {c : F} (hB3 : B ^ 3 = 1) (hc : c ^ 3 = 1) :
    B * Eig B c = c • Eig B c := by
  have hBBB : B * B ^ 2 = 1 := by
    rw [← hB3]
    exact (pow_succ' B 2).symm
  have hBsq : B * B = B ^ 2 := (sq B).symm
  have hc2 : c * c ^ 2 = 1 := by
    rw [← hc]
    ring
  have hcc : c * c = c ^ 2 := by ring
  unfold Eig
  rw [mul_add, mul_add, mul_one, Matrix.mul_smul, Matrix.mul_smul, hBsq, hBBB, smul_add, smul_add,
    smul_smul, smul_smul, hc2, hcc, one_smul]
  abel

theorem B_mulVec_Eig {B : Matrix (Fin 6) (Fin 6) F} {c : F} (hB3 : B ^ 3 = 1) (hc : c ^ 3 = 1)
    (a : Fin 6 → F) : B *ᵥ (Eig B c *ᵥ a) = c • (Eig B c *ᵥ a) := by
  rw [Matrix.mulVec_mulVec, B_mul_Eig hB3 hc, Matrix.smul_mulVec]

theorem Eig_mul_self {B : Matrix (Fin 6) (Fin 6) F} {c : F} (hB3 : B ^ 3 = 1) (hc : c ^ 3 = 1) :
    Eig B c * Eig B c = Eig B c := by
  have hBE : B * Eig B c = c • Eig B c := B_mul_Eig hB3 hc
  have hB2E : B ^ 2 * Eig B c = (c * c) • Eig B c := by
    rw [sq, mul_assoc, hBE, Matrix.mul_smul, hBE, smul_smul]
  show (1 + c ^ 2 • B + c • B ^ 2) * Eig B c = Eig B c
  rw [add_mul, add_mul, one_mul, smul_mul_assoc, smul_mul_assoc, hBE, hB2E, smul_smul, smul_smul,
    add_assoc, ← add_smul,
    show c ^ 2 * c + c * (c * c) = 0 by linear_combination c ^ 3 * (two_eq_zero' (F := F)), zero_smul,
    add_zero]

theorem commute_Eig {Y B : Matrix (Fin 6) (Fin 6) F} (hYB : Commute Y B) (c : F) :
    Commute Y (Eig B c) := by
  unfold Eig
  exact ((Commute.one_right Y).add_right (hYB.smul_right _)).add_right ((hYB.pow_right 2).smul_right _)

theorem Eig_sum {ω : F} (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) (B : Matrix (Fin 6) (Fin 6) F) :
    Eig B 1 + Eig B ω + Eig B (ω ^ 2) = 1 := by
  have hs : (1 : F) + ω + ω ^ 2 = 0 := one_add_omega_add_sq hω3 hω1
  have h4 : (1 : F) + ω ^ 2 + (ω ^ 2) ^ 2 = 0 := by linear_combination hs + ω * hω3
  have h3 : (1 : F) + 1 + 1 = 1 := by linear_combination (two_eq_zero' (F := F))
  unfold Eig
  have e : (1 + (1 : F) ^ 2 • B + (1 : F) • B ^ 2) + (1 + ω ^ 2 • B + ω • B ^ 2) +
      (1 + (ω ^ 2) ^ 2 • B + ω ^ 2 • B ^ 2) =
      ((1 : F) + 1 + 1) • (1 : Matrix (Fin 6) (Fin 6) F) + ((1 : F) + ω ^ 2 + (ω ^ 2) ^ 2) • B +
        ((1 : F) + ω + ω ^ 2) • B ^ 2 := by
    module
  rw [e, h3, h4, hs, one_smul, zero_smul, zero_smul, add_zero, add_zero]

theorem Eig_sum_range {ω : F} (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) (B : Matrix (Fin 6) (Fin 6) F) :
    ∑ k ∈ Finset.range 3, Eig B (ω ^ k) = 1 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, pow_one]
  exact Eig_sum hω3 hω1 B

theorem Eig_decomp {ω : F} (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) (B : Matrix (Fin 6) (Fin 6) F)
    (v : Fin 6 → F) : ∑ k ∈ Finset.range 3, Eig B (ω ^ k) *ᵥ v = v := by
  rw [← Matrix.sum_mulVec, Eig_sum_range hω3 hω1 B, Matrix.one_mulVec]

theorem herm2_eigen_orth {B : Matrix (Fin 6) (Fin 6) F}
    (hB : ∀ a b : Fin 6 → F, herm2 (B *ᵥ a) (B *ᵥ b) = herm2 a b) {c d : F} {u w : Fin 6 → F}
    (hu : B *ᵥ u = c • u) (hw : B *ᵥ w = d • w) (hcd : c ^ 2 * d ≠ 1) : herm2 u w = 0 := by
  have h := hB u w
  rw [hu, hw, herm2_smul_left, herm2_smul_right] at h
  have h2 : (c ^ 2 * d - 1) * herm2 u w = 0 := by linear_combination h
  rcases mul_eq_zero.1 h2 with h1 | h1
  · exact absurd (sub_eq_zero.1 h1) hcd
  · exact h1

theorem Eig_orth {ω : F} {B : Matrix (Fin 6) (Fin 6) F}
    (hB : ∀ a b : Fin 6 → F, herm2 (B *ᵥ a) (B *ᵥ b) = herm2 a b) (hB3 : B ^ 3 = 1) (hω3 : ω ^ 3 = 1)
    (hω1 : ω ≠ 1) {j k : ℕ} (hk : k < 3) (hj : j < 3) (hjk : j ≠ k) (a b : Fin 6 → F) :
    herm2 (Eig B (ω ^ j) *ᵥ a) (Eig B (ω ^ k) *ᵥ b) = 0 := by
  refine herm2_eigen_orth hB (B_mulVec_Eig hB3 (cube_pow_eq_one hω3 j) a)
    (B_mulVec_Eig hB3 (cube_pow_eq_one hω3 k) b) ?_
  rw [← pow_mul, ← pow_add]
  exact pow_ne_one_of_mod hω3 hω1 _ (by omega)

theorem Eig_selfadj_left {ω : F} {B : Matrix (Fin 6) (Fin 6) F}
    (hB : ∀ a b : Fin 6 → F, herm2 (B *ᵥ a) (B *ᵥ b) = herm2 a b) (hB3 : B ^ 3 = 1) (hω3 : ω ^ 3 = 1)
    (hω1 : ω ≠ 1) {j : ℕ} (hj : j < 3) (a b : Fin 6 → F) :
    herm2 (Eig B (ω ^ j) *ᵥ a) b = herm2 (Eig B (ω ^ j) *ᵥ a) (Eig B (ω ^ j) *ᵥ b) := by
  conv_lhs => rw [← Eig_decomp hω3 hω1 B b]
  rw [herm2_sum_right, Finset.sum_eq_single j]
  · intro k hk hkj
    exact Eig_orth hB hB3 hω3 hω1 (Finset.mem_range.1 hk) hj (Ne.symm hkj) a b
  · intro h
    exact absurd (Finset.mem_range.2 hj) h

theorem Eig_selfadj_right {ω : F} {B : Matrix (Fin 6) (Fin 6) F}
    (hB : ∀ a b : Fin 6 → F, herm2 (B *ᵥ a) (B *ᵥ b) = herm2 a b) (hB3 : B ^ 3 = 1) (hω3 : ω ^ 3 = 1)
    (hω1 : ω ≠ 1) {j : ℕ} (hj : j < 3) (a b : Fin 6 → F) :
    herm2 a (Eig B (ω ^ j) *ᵥ b) = herm2 (Eig B (ω ^ j) *ᵥ a) (Eig B (ω ^ j) *ᵥ b) := by
  conv_lhs => rw [← Eig_decomp hω3 hω1 B a]
  rw [herm2_sum_left, Finset.sum_eq_single j]
  · intro k hk hkj
    exact Eig_orth hB hB3 hω3 hω1 hj (Finset.mem_range.1 hk) hkj a b
  · intro h
    exact absurd (Finset.mem_range.2 hj) h

theorem eq_one_of_isometry_commute {ω : F} (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) (hF4 : ∀ x : F, x ^ 4 = x)
    {B Y : Matrix (Fin 6) (Fin 6) F}
    (hU : (B.map (fun x : F => x ^ 2))ᵀ * B = 1) (hB3 : B ^ 3 = 1) (hBns : ∀ c : F, B ≠ c • 1)
    (hY : ∀ a b : Fin 6 → F, herm2 (Y *ᵥ a) (Y *ᵥ b) = herm2 a b) (hY7 : Y ^ 7 = 1)
    (hYB : Commute Y B) : Y = 1 := by
  have hB : ∀ a b : Fin 6 → F, herm2 (B *ᵥ a) (B *ᵥ b) = herm2 a b := herm2_unitary hU
  have hne : ∀ j < 3, Eig B (ω ^ j) ≠ 1 := by
    intro j _ h
    apply hBns (ω ^ j)
    have h' := B_mul_Eig hB3 (cube_pow_eq_one hω3 j)
    rw [h, mul_one] at h'
    exact h'
  have hkey : ∀ j < 3, ∀ v : Fin 6 → F, Y *ᵥ (Eig B (ω ^ j) *ᵥ v) = Eig B (ω ^ j) *ᵥ v := by
    intro j hj v
    have hP2 : ∀ w : Fin 6 → F, Eig B (ω ^ j) *ᵥ (Eig B (ω ^ j) *ᵥ w) = Eig B (ω ^ j) *ᵥ w := by
      intro w
      rw [Matrix.mulVec_mulVec, Eig_mul_self hB3 (cube_pow_eq_one hω3 j)]
    obtain ⟨v0, hv0⟩ : ∃ v0 : Fin 6 → F, Eig B (ω ^ j) *ᵥ v0 ≠ v0 := by
      by_contra hcon
      push_neg at hcon
      apply hne j hj
      exact Matrix.ext_iff_mulVec.2 fun w => by rw [Matrix.one_mulVec]; exact hcon w
    refine key_lemma2 hF4 hY hY7 (commute_Eig hYB _)
      (fun a b => (Eig_selfadj_left hB hB3 hω3 hω1 hj a b).trans (Eig_selfadj_right hB hB3 hω3 hω1 hj a b).symm)
      hP2 (t := v0 - Eig B (ω ^ j) *ᵥ v0) ?_ ?_ v
    · intro h
      exact hv0 (sub_eq_zero.1 h).symm
    · rw [Matrix.mulVec_sub, hP2, sub_self]
  have hY1 : ∀ v : Fin 6 → F, Y *ᵥ v = v := by
    intro v
    have hv := Eig_decomp hω3 hω1 B v
    calc Y *ᵥ v = Y *ᵥ (∑ k ∈ Finset.range 3, Eig B (ω ^ k) *ᵥ v) := by rw [hv]
      _ = ∑ k ∈ Finset.range 3, Y *ᵥ (Eig B (ω ^ k) *ᵥ v) := Matrix.mulVec_sum _ _ _
      _ = ∑ k ∈ Finset.range 3, Eig B (ω ^ k) *ᵥ v :=
          Finset.sum_congr rfl fun k hk => hkey k (Finset.mem_range.1 hk) v
      _ = v := hv
  exact Matrix.ext_iff_mulVec.2 fun v => by rw [Matrix.one_mulVec]; exact hY1 v

end CFSG.LocalAnalysis.GLTheoremA.HU7

end
