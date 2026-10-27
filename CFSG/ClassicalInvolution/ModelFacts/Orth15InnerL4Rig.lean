module

public import CFSG.ClassicalInvolution.ModelFacts.Orth15InnerL4X

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Orth15.InnerL4

open Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterL4
open scoped MatrixGroups

variable {F : Type} [Field F]

theorem trace_U1 : (((U1 F : SL(4, F)) : Matrix (Fin 4) (Fin 4) F)).trace = 4 := by
  rw [coe_U1]
  simp [Matrix.trace, Fin.sum_univ_four]
  norm_num

theorem aut_fix_blocks_U1 [Finite F] (h2 : (2 : F) ≠ 0) (φ : MulAut (projectiveSL 4 F))
    (hfix : ∀ r ∈ (blockSL F 4 2 0 (by norm_num)).range, φ (proj 4 F r) = proj 4 F r)
    (hfix' : ∀ r ∈ (blockSL F 4 2 2 (by norm_num)).range, φ (proj 4 F r) = proj 4 F r)
    (hU : φ (proj 4 F (U1 F)) = proj 4 F (U1 F)) : φ = 1 ∨ φ * φ = 1 := by
  obtain ⟨-, hform⟩ := automorphism_generation (K := F) (n := 4) (by norm_num)
  obtain ⟨A, σ, ε, hε, hαeq⟩ := hform φ
  interval_cases ε
  · rw [pow_zero, mul_one] at hαeq
    subst hαeq
    obtain ⟨hσ, a, b, ha, hb, hM⟩ := aut_fix_blocks_zero h2 A σ hfix hfix'
    subst hσ
    have h1 : fieldAut 4 F (RingEquiv.refl F) = 1 := map_one _
    rw [h1, mul_one] at hU ⊢
    left
    have hrel := exact_rel_conj (four_ne_zero h2) A hU trace_U1
    rw [hM, coe_U1] at hrel
    have e := congrFun (congrFun hrel 0) 2
    simp [Matrix.mul_apply, Fin.sum_univ_four] at e
    have hab : a = b := e.symm
    rw [conjAut_eq_of_smul A 1 a ha ?_, map_one]
    rw [hM, hab, Units.val_one]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  · rw [pow_one] at hαeq
    subst hαeq
    obtain ⟨hσ, m, n, hm, hn, hM⟩ := aut_fix_blocks_one h2 A σ hfix hfix'
    subst hσ
    have h1 : fieldAut 4 F (RingEquiv.refl F) = 1 := map_one _
    rw [h1, mul_one]
    right
    exact sq_of_antidiag A m n hm hn hM

theorem eq_one_of_pow_odd {G : Type*} [Group G] {g : G} {n : ℕ} (hn : Odd n) (hgn : g ^ n = 1)
    (hsq : g * g = 1) : g = 1 := by
  obtain ⟨k, rfl⟩ := hn
  rw [pow_succ, pow_mul, pow_two, hsq, one_pow, one_mul] at hgn
  exact hgn

theorem eq_one_of_fix_U1 [Finite F] (h2 : (2 : F) ≠ 0) (φ : MulAut (projectiveSL 4 F)) {n : ℕ}
    (hn : Odd n) (hφn : φ ^ n = 1)
    (hfix : ∀ r ∈ (blockSL F 4 2 0 (by norm_num)).range, φ (proj 4 F r) = proj 4 F r)
    (hfix' : ∀ r ∈ (blockSL F 4 2 2 (by norm_num)).range, φ (proj 4 F r) = proj 4 F r)
    (hU : φ (proj 4 F (U1 F)) = proj 4 F (U1 F)) : φ = 1 := by
  rcases aut_fix_blocks_U1 h2 φ hfix hfix' hU with h | h
  · exact h
  · exact eq_one_of_pow_odd hn hφn h

end CFSG.ClassicalInvolution.ModelFacts.Orth15.InnerL4
