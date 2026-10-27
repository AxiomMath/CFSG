module

public import CFSG.ClassicalInvolution.ModelFacts.Orth15OuterL4

public section

namespace CFSG.ClassicalInvolution.Asc77.CX.CX4.L4

open Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterL4
open scoped MatrixGroups

variable {F : Type} [Field F]

@[expose] def FixBlocks (β : MulAut (projectiveSL 4 F)) : Prop :=
  (∀ r ∈ (blockSL F 4 2 0 (by norm_num)).range, β (proj 4 F r) = proj 4 F r) ∧
    ∀ r ∈ (blockSL F 4 2 2 (by norm_num)).range, β (proj 4 F r) = proj 4 F r

noncomputable abbrev zbar : projectiveSL 4 F := proj 4 F (rootInv F (show 2 ≤ 4 by norm_num))

theorem fix_cases [Finite F] (h2 : (2 : F) ≠ 0) {β : MulAut (projectiveSL 4 F)}
    (hβ : FixBlocks β) :
    (∃ A : GL (Fin 4) F, ∃ a b : F, a ≠ 0 ∧ b ≠ 0 ∧
      (A : Matrix (Fin 4) (Fin 4) F) = !![a, 0, 0, 0; 0, a, 0, 0; 0, 0, b, 0; 0, 0, 0, b] ∧
      β = conjAut 4 F A) ∨
    (∃ A : GL (Fin 4) F, ∃ m n : F, m ≠ 0 ∧ n ≠ 0 ∧
      (A : Matrix (Fin 4) (Fin 4) F) = !![0, m, 0, 0; -m, 0, 0, 0; 0, 0, 0, n; 0, 0, -n, 0] ∧
      β = conjAut 4 F A * dualAut 4 F) := by
  obtain ⟨-, hform⟩ := automorphism_generation (K := F) (n := 4) (by norm_num)
  obtain ⟨A, σ, ε, hε, hβeq⟩ := hform β
  have h1 : fieldAut 4 F (RingEquiv.refl F) = 1 := map_one _
  interval_cases ε
  · rw [pow_zero, mul_one] at hβeq
    subst hβeq
    obtain ⟨hσ, a, b, ha, hb, hM⟩ := aut_fix_blocks_zero h2 A σ hβ.1 hβ.2
    subst hσ
    exact Or.inl ⟨A, a, b, ha, hb, hM, by rw [h1, mul_one]⟩
  · rw [pow_one] at hβeq
    subst hβeq
    obtain ⟨hσ, m, n, hm, hn, hM⟩ := aut_fix_blocks_one h2 A σ hβ.1 hβ.2
    subst hσ
    exact Or.inr ⟨A, m, n, hm, hn, hM, by rw [h1, mul_one]⟩

omit [Field F] in
theorem sq_eq_one_of_pow_two_pow {F : Type} [Field F] (hsq : ¬ IsSquare (-1 : F)) {t : F} :
    ∀ {k : ℕ}, t ^ (2 ^ k) = 1 → t ^ 2 = 1
  | 0, h => by
    rw [pow_zero, pow_one] at h
    rw [h, one_pow]
  | k + 1, h => by
    have h' : (t ^ 2) ^ (2 ^ k) = 1 := by
      rw [← pow_mul, ← pow_succ']
      exact h
    have h4 : (t ^ 2) ^ 2 = 1 := sq_eq_one_of_pow_two_pow hsq h'
    have h5 : (t ^ 2 - 1) * (t ^ 2 + 1) = 0 := by linear_combination h4
    rcases mul_eq_zero.mp h5 with h6 | h6
    · linear_combination h6
    · exact absurd ⟨t, by linear_combination -h6⟩ hsq

theorem diag4_eq (a b c d : F) :
    (!![a, 0, 0, 0; 0, b, 0, 0; 0, 0, c, 0; 0, 0, 0, d] : Matrix (Fin 4) (Fin 4) F) =
      Matrix.diagonal ![a, b, c, d] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem coe_pow_diag (A : GL (Fin 4) F) {a b : F}
    (hM : (A : Matrix (Fin 4) (Fin 4) F) = !![a, 0, 0, 0; 0, a, 0, 0; 0, 0, b, 0; 0, 0, 0, b])
    (N : ℕ) : ((A ^ N : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      !![a ^ N, 0, 0, 0; 0, a ^ N, 0, 0; 0, 0, b ^ N, 0; 0, 0, 0, b ^ N] := by
  rw [Units.val_pow_eq_pow_val, hM, diag4_eq, diag4_eq, Matrix.diagonal_pow]
  congr 1
  ext i
  fin_cases i <;> rfl

theorem conjAut_diag_of_sq (A : GL (Fin 4) F) {a b : F} (ha : a ≠ 0)
    (hM : (A : Matrix (Fin 4) (Fin 4) F) = !![a, 0, 0, 0; 0, a, 0, 0; 0, 0, b, 0; 0, 0, 0, b])
    (hab : b ^ 2 = a ^ 2) : conjAut 4 F A = 1 ∨ conjAut 4 F A = MulAut.conj zbar := by
  have h' : (b - a) * (b + a) = 0 := by linear_combination hab
  rcases mul_eq_zero.mp h' with h | h
  · left
    have hb : b = a := by linear_combination h
    rw [conjAut_eq_of_smul A 1 a ha ?_, map_one]
    rw [hM, hb]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  · right
    have hb : b = -a := by linear_combination h
    rw [conjAut_eq_of_smul A (Matrix.SpecialLinearGroup.toGL (rootInv F
      (show 2 ≤ 4 by norm_num))) (-a) (neg_ne_zero.mpr ha) ?_,
      CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterL4.conjAut_toGL]
    rw [hM, coe_toGL_rootInv, hb]
    ext i j
    fin_cases i <;> fin_cases j <;> simp

theorem diag_two_elem (h2 : (2 : F) ≠ 0) (hsq : ¬ IsSquare (-1 : F)) (A : GL (Fin 4) F)
    {a b : F} (ha : a ≠ 0)
    (hM : (A : Matrix (Fin 4) (Fin 4) F) = !![a, 0, 0, 0; 0, a, 0, 0; 0, 0, b, 0; 0, 0, 0, b])
    {k : ℕ} (hk : conjAut 4 F A ^ (2 ^ k) = 1) :
    conjAut 4 F A = 1 ∨ conjAut 4 F A = MulAut.conj zbar := by
  have h4 := four_ne_zero h2
  rw [← map_pow] at hk
  have hrel := exact_rel_conj h4 (A ^ (2 ^ k)) (r := u02 1) (by rw [hk]; rfl) (trace_u02 1)
  rw [coe_pow_diag A hM] at hrel
  have e := congrFun (congrFun hrel 0) 2
  simp [u02, Matrix.mul_apply, Fin.sum_univ_four] at e
  have ht : (b / a) ^ (2 ^ k) = 1 := by
    rw [div_pow, e, div_self (pow_ne_zero _ ha)]
  have ht2 := sq_eq_one_of_pow_two_pow hsq ht
  refine conjAut_diag_of_sq A ha hM ?_
  rw [div_pow, div_eq_one_iff_eq (pow_ne_zero _ ha)] at ht2
  exact ht2

theorem inv_antidiag (B : GL (Fin 4) F) {m n : F} (hm : m ≠ 0) (hn : n ≠ 0)
    (hB : (B : Matrix (Fin 4) (Fin 4) F) =
      !![0, m, 0, 0; -m, 0, 0, 0; 0, 0, 0, n; 0, 0, -n, 0]) :
    ((B⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      !![0, -m⁻¹, 0, 0; m⁻¹, 0, 0, 0; 0, 0, 0, -n⁻¹; 0, 0, n⁻¹, 0] := by
  rw [Matrix.coe_units_inv, hB]
  refine Matrix.inv_eq_right_inv ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four, hm, hn]

theorem graph_mul_graph (A B : GL (Fin 4) F) {m n m' n' : F} (hm' : m' ≠ 0) (hn' : n' ≠ 0)
    (hA : (A : Matrix (Fin 4) (Fin 4) F) =
      !![0, m, 0, 0; -m, 0, 0, 0; 0, 0, 0, n; 0, 0, -n, 0])
    (hB : (B : Matrix (Fin 4) (Fin 4) F) =
      !![0, m', 0, 0; -m', 0, 0, 0; 0, 0, 0, n'; 0, 0, -n', 0]) :
    conjAut 4 F A * dualAut 4 F * (conjAut 4 F B * dualAut 4 F) =
      conjAut 4 F (A * Matrix.GeneralLinearGroup.inverseTranspose B) ∧
    ((A * Matrix.GeneralLinearGroup.inverseTranspose B : GL (Fin 4) F) :
      Matrix (Fin 4) (Fin 4) F) = !![-(m / m'), 0, 0, 0; 0, -(m / m'), 0, 0;
        0, 0, -(n / n'), 0; 0, 0, 0, -(n / n')] := by
  obtain ⟨-, -, -, -, hdc, -⟩ := standard_automorphism_transport (n := 4) (K := F)
  refine ⟨?_, ?_⟩
  · calc conjAut 4 F A * dualAut 4 F * (conjAut 4 F B * dualAut 4 F)
        = conjAut 4 F A * (dualAut 4 F * conjAut 4 F B * dualAut 4 F) := by group
      _ = conjAut 4 F (A * Matrix.GeneralLinearGroup.inverseTranspose B) := by
        rw [hdc B, map_mul]
  · rw [Units.val_mul, Matrix.GeneralLinearGroup.coe_inverseTranspose, inv_antidiag B hm' hn' hB,
      hA]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four] <;> field_simp

theorem conj_zbar_sq : MulAut.conj (zbar (F := F)) * MulAut.conj zbar = 1 := by
  rw [← map_mul, zbar, ← map_mul, rootInv, ← map_mul, neg_one_mul, neg_neg, map_one, map_one,
    map_one]

theorem two_elem_cases [Finite F] (h2 : (2 : F) ≠ 0) (hsq : ¬ IsSquare (-1 : F))
    {β : MulAut (projectiveSL 4 F)} (hβ : FixBlocks β) {k : ℕ} (hk : β ^ (2 ^ k) = 1) :
    (β = 1 ∨ β = MulAut.conj zbar) ∨
    (∃ A : GL (Fin 4) F, ∃ m n : F, m ≠ 0 ∧ n ≠ 0 ∧
      (A : Matrix (Fin 4) (Fin 4) F) = !![0, m, 0, 0; -m, 0, 0, 0; 0, 0, 0, n; 0, 0, -n, 0] ∧
      β = conjAut 4 F A * dualAut 4 F) := by
  rcases fix_cases h2 hβ with ⟨A, a, b, ha, -, hM, rfl⟩ | h
  · exact Or.inl (diag_two_elem h2 hsq A ha hM hk)
  · exact Or.inr h

theorem graph_sq (A : GL (Fin 4) F) {m n : F} (hm : m ≠ 0) (hn : n ≠ 0)
    (hA : (A : Matrix (Fin 4) (Fin 4) F) =
      !![0, m, 0, 0; -m, 0, 0, 0; 0, 0, 0, n; 0, 0, -n, 0]) :
    conjAut 4 F A * dualAut 4 F * (conjAut 4 F A * dualAut 4 F) = 1 :=
  sq_of_antidiag A m n hm hn hA

theorem fix_pgroup [Finite F] (h2 : (2 : F) ≠ 0) (hsq : ¬ IsSquare (-1 : F))
    (P : Subgroup (MulAut (projectiveSL 4 F))) (hP : IsPGroup 2 P)
    (hfix : ∀ β ∈ P, FixBlocks β) : (∀ β ∈ P, β * β = 1) ∧ Nat.card P ≤ 4 := by
  classical
  have hpow : ∀ β ∈ P, ∃ k : ℕ, β ^ (2 ^ k) = 1 := fun β hβ => by
    obtain ⟨k, hk⟩ := hP ⟨β, hβ⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hcase : ∀ β ∈ P, (β = 1 ∨ β = MulAut.conj zbar) ∨
      (∃ A : GL (Fin 4) F, ∃ m n : F, m ≠ 0 ∧ n ≠ 0 ∧
        (A : Matrix (Fin 4) (Fin 4) F) = !![0, m, 0, 0; -m, 0, 0, 0; 0, 0, 0, n; 0, 0, -n, 0] ∧
        β = conjAut 4 F A * dualAut 4 F) := fun β hβ => by
    obtain ⟨k, hk⟩ := hpow β hβ
    exact two_elem_cases h2 hsq (hfix β hβ) hk
  have hsq' : ∀ β ∈ P, β * β = 1 := by
    intro β hβ
    rcases hcase β hβ with (rfl | rfl) | ⟨A, m, n, hm, hn, hA, rfl⟩
    · exact mul_one 1
    · exact conj_zbar_sq
    · exact graph_sq A hm hn hA
  refine ⟨hsq', ?_⟩
  have hcard : ∀ S : Finset (MulAut (projectiveSL 4 F)), S.card ≤ 4 →
      (P : Set (MulAut (projectiveSL 4 F))) ⊆ ↑S → Nat.card P ≤ 4 := by
    intro S hS hsub
    have h := Nat.card_mono (Set.toFinite _) hsub
    have e : Nat.card (↑S : Set (MulAut (projectiveSL 4 F))) = S.card := by
      rw [Nat.card_coe_set_eq, Set.ncard_coe_finset]
    calc Nat.card P = Nat.card (P : Set (MulAut (projectiveSL 4 F))) := rfl
      _ ≤ Nat.card (↑S : Set (MulAut (projectiveSL 4 F))) := h
      _ = S.card := e
      _ ≤ 4 := hS
  by_cases hγ : ∃ γ ∈ P, ∃ A : GL (Fin 4) F, ∃ m n : F, m ≠ 0 ∧ n ≠ 0 ∧
      (A : Matrix (Fin 4) (Fin 4) F) = !![0, m, 0, 0; -m, 0, 0, 0; 0, 0, 0, n; 0, 0, -n, 0] ∧
      γ = conjAut 4 F A * dualAut 4 F
  · obtain ⟨γ, hγP, A, m, n, hm, hn, hA, hγA⟩ := hγ
    have hγ2 : γ * γ = 1 := hsq' γ hγP
    refine hcard {1, MulAut.conj zbar, γ, γ * MulAut.conj zbar} (Finset.card_le_four) ?_
    intro β hβ
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    rcases hcase β hβ with (h | h) | ⟨B, m', n', hm', hn', hB, hβB⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · obtain ⟨heq, hC⟩ := graph_mul_graph A B hm' hn' hA hB
      have hγβ : γ * β ∈ P := mul_mem hγP hβ
      obtain ⟨k, hk⟩ := hpow _ hγβ
      rw [hγA, hβB, heq] at hk
      have hne : -(m / m') ≠ 0 := neg_ne_zero.mpr (div_ne_zero hm hm')
      have hγβ' : γ * β = conjAut 4 F (A * Matrix.GeneralLinearGroup.inverseTranspose B) := by
        rw [hγA, hβB, heq]
      have hβeq : β = γ * (γ * β) := by rw [← mul_assoc, hγ2, one_mul]
      rcases diag_two_elem h2 hsq _ hne hC hk with h | h
      · rw [← hγβ'] at h
        right; right; left
        rw [hβeq, h, mul_one]
      · rw [← hγβ'] at h
        right; right; right
        rw [hβeq, h]
  · refine hcard {1, MulAut.conj zbar} (Finset.card_le_two.trans (by norm_num)) ?_
    intro β hβ
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    rcases hcase β hβ with (h | h) | ⟨B, m', n', hm', hn', hB, hβB⟩
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd ⟨β, hβ, B, m', n', hm', hn', hB, hβB⟩ hγ

end CFSG.ClassicalInvolution.Asc77.CX.CX4.L4
