module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotAutUCenter

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Assembly.LowTwoRank
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (upperUnipotentSp)

variable {K : Type} [Field K]

@[expose] def spARepMat (n j : ℕ) : Matrix (Fin n) (Fin n) K :=
  Matrix.of fun a b =>
    if a.val / 2 = b.val / 2 ∧ a ≠ b ∧ a.val < 2 * j ∧ b.val < 2 * j then 1 else 0

theorem spARepMat_transpose (n j : ℕ) :
    (spARepMat n j : Matrix (Fin n) (Fin n) K)ᵀ = spARepMat n j := by
  ext a b
  simp only [transpose_apply, spARepMat, of_apply]
  by_cases h : a.val / 2 = b.val / 2 ∧ a ≠ b ∧ a.val < 2 * j ∧ b.val < 2 * j
  · rw [ite_eq_left h, ite_eq_left ⟨h.1.symm, h.2.1.symm, h.2.2.2, h.2.2.1⟩]
  · rw [ite_eq_right h, ite_eq_right fun h' => h ⟨h'.1.symm, h'.2.1.symm, h'.2.2.2, h'.2.2.1⟩]

@[expose] noncomputable def spARep (n j : ℕ) : StatedSp n K :=
  upperUnipotentSp n K (spARepMat_transpose n j)

theorem spARep_mul_self [CharP K 2] (n j : ℕ) : spARep n j * spARep n j = (1 : StatedSp n K) := by
  apply mat_injective
  rw [map_mul, spARep, mat_upperUnipotentSp, map_one, fromBlocks_multiply]
  have hCC : (spARepMat n j : Matrix (Fin n) (Fin n) K) + spARepMat n j = 0 := by
    ext a b
    rw [Matrix.add_apply, Matrix.zero_apply]
    exact CharTwo.add_self_eq_zero _
  simp only [Matrix.one_mul, Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
    hCC]
  exact fromBlocks_one

@[expose] def spAExp (n j : ℕ) : ℕ :=
  n ^ 2 - j ^ 2 + j

theorem spAExp_succ_add {n j : ℕ} (hj : j + 1 ≤ n) : spAExp n (j + 1) + 2 * j = spAExp n j := by
  have h1 : (j + 1) ^ 2 ≤ n ^ 2 := Nat.pow_le_pow_left hj 2
  have h2 : j ^ 2 ≤ n ^ 2 := Nat.pow_le_pow_left (by omega) 2
  unfold spAExp
  zify [h1, h2]
  ring

theorem spAExp_lt_of_lt {n j j' : ℕ} (hj : 1 ≤ j) (hjj : j < j') (hj' : j' ≤ n) :
    spAExp n j' < spAExp n j := by
  induction j' with
  | zero => omega
  | succ m ih =>
    have e := spAExp_succ_add (n := n) (j := m) hj'
    rcases Nat.lt_succ_iff_lt_or_eq.1 hjj with h | h
    · have := ih h (by omega)
      omega
    · subst h
      omega

@[expose] def SpACentralizerPerfectInput : Prop :=
  ∀ (n j : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], 4 ≤ Nat.card K → 1 ≤ j → 2 * j ≤ n →
    ⁅centralizer ({spARep n j} : Set (StatedSp n K)),
      centralizer ({spARep n j} : Set (StatedSp n K))⁆ =
      centralizer ({spARep n j} : Set (StatedSp n K))

@[expose] def SpACentralizerTwoPartInput : Prop :=
  ∀ (n j f : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 ^ f → 2 * j ≤ n →
    (Nat.card (centralizer ({spARep n j} : Set (StatedSp n K)))).factorization 2 = f * spAExp n j

end CFSG.SeitzReduction.SymplecticPilot
