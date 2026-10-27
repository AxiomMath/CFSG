module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk94G4ExL4

public section

namespace CFSG.GH74.GLS.IVK.Proofs2.Ivk94

open Matrix Subgroup CFSG CFSG.GH74 CFSG.Blueprint CFSG.Assembly.LowTwoRank

namespace PSp4

section Matrices

variable {F : Type} [Field F]

@[expose] def spX : Matrix (Fin 2) (Fin 2) F := !![0, 1; 1, 0]

@[expose] def spZ : Matrix (Fin 2) (Fin 2) F := !![1, 0; 0, -1]

theorem spX_mul_spX : (spX : Matrix (Fin 2) (Fin 2) F) * spX = 1 := by
  ext k l; fin_cases k <;> fin_cases l <;> simp [spX, Matrix.mul_apply, Fin.sum_univ_succ]

theorem spZ_mul_spZ : (spZ : Matrix (Fin 2) (Fin 2) F) * spZ = 1 := by
  ext k l; fin_cases k <;> fin_cases l <;> simp [spZ, Matrix.mul_apply, Fin.sum_univ_succ]

theorem spX_mul_spZ : (spX : Matrix (Fin 2) (Fin 2) F) * spZ = -(spZ * spX) := by
  ext k l; fin_cases k <;> fin_cases l <;> simp [spX, spZ, Matrix.mul_apply, Fin.sum_univ_succ]

theorem spX_transpose : (spX : Matrix (Fin 2) (Fin 2) F)ᵀ = spX := by
  ext k l; fin_cases k <;> fin_cases l <;> simp [spX]

theorem spZ_transpose : (spZ : Matrix (Fin 2) (Fin 2) F)ᵀ = spZ := by
  ext k l; fin_cases k <;> fin_cases l <;> simp [spZ]

@[expose] def sp0 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F := fromBlocks 0 1 (-1) 0

@[expose] def sp1 (α β : F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F :=
  fromBlocks (α • 1) (β • 1) (β • 1) ((-α) • 1)

@[expose] def sp2 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F := fromBlocks spX 0 0 spX

@[expose] def sp3 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F := fromBlocks spZ 0 0 spZ

theorem fb_mul_self {A B C D : Matrix (Fin 2) (Fin 2) F} {c : F}
    (h₁ : A * A + B * C = c • 1) (h₂ : A * B + B * D = 0) (h₃ : C * A + D * C = 0)
    (h₄ : C * B + D * D = c • 1) :
    fromBlocks A B C D * fromBlocks A B C D =
      c • (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) := by
  rw [fromBlocks_multiply, ← fromBlocks_one, fromBlocks_smul, h₁, h₂, h₃, h₄, smul_zero]

theorem fb_mul_comm {A B C D A' B' C' D' : Matrix (Fin 2) (Fin 2) F}
    (h₁ : A * A' + B * C' = A' * A + B' * C) (h₂ : A * B' + B * D' = A' * B + B' * D)
    (h₃ : C * A' + D * C' = C' * A + D' * C) (h₄ : C * B' + D * D' = C' * B + D' * D) :
    fromBlocks A B C D * fromBlocks A' B' C' D' = fromBlocks A' B' C' D' * fromBlocks A B C D := by
  rw [fromBlocks_multiply, fromBlocks_multiply, h₁, h₂, h₃, h₄]

theorem fb_mul_anticomm {A B C D A' B' C' D' : Matrix (Fin 2) (Fin 2) F}
    (h₁ : A * A' + B * C' = -(A' * A + B' * C)) (h₂ : A * B' + B * D' = -(A' * B + B' * D))
    (h₃ : C * A' + D * C' = -(C' * A + D' * C)) (h₄ : C * B' + D * D' = -(C' * B + D' * D)) :
    fromBlocks A B C D * fromBlocks A' B' C' D' =
      -(fromBlocks A' B' C' D' * fromBlocks A B C D) := by
  rw [fromBlocks_multiply, fromBlocks_multiply, fromBlocks_neg, h₁, h₂, h₃, h₄]

theorem sc_mul_sc (a b : F) : (a • 1 : Matrix (Fin 2) (Fin 2) F) * (b • 1) = (a * b) • 1 := by
  rw [Matrix.smul_mul, Matrix.one_mul, smul_smul]

theorem sp0_mul_sp0 : (sp0 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) * sp0 = (-1 : F) • 1 :=
  fb_mul_self (by simp) (by simp) (by simp) (by simp)

theorem sp1_mul_sp1 {α β : F} (h : α ^ 2 + β ^ 2 = -1) :
    (sp1 α β : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) * sp1 α β = (-1 : F) • 1 := by
  refine fb_mul_self ?_ ?_ ?_ ?_
  · rw [sc_mul_sc, sc_mul_sc, ← add_smul]
    congr 1
    linear_combination h
  · rw [sc_mul_sc, sc_mul_sc, ← add_smul]
    rw [show α * β + β * -α = 0 by ring, zero_smul]
  · rw [sc_mul_sc, sc_mul_sc, ← add_smul]
    rw [show β * α + -α * β = 0 by ring, zero_smul]
  · rw [sc_mul_sc, sc_mul_sc, ← add_smul]
    congr 1
    linear_combination h

theorem sp2_mul_sp2 : (sp2 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) * sp2 = (1 : F) • 1 :=
  fb_mul_self (by simp [spX_mul_spX]) (by simp) (by simp) (by simp [spX_mul_spX])

theorem sp3_mul_sp3 : (sp3 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) * sp3 = (1 : F) • 1 :=
  fb_mul_self (by simp [spZ_mul_spZ]) (by simp) (by simp) (by simp [spZ_mul_spZ])

theorem sp_comm01 (α β : F) : (sp0 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) * sp1 α β =
    -(sp1 α β * sp0) :=
  fb_mul_anticomm (by simp) (by simp) (by simp) (by simp)

theorem sp_comm02 : (sp0 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) * sp2 = sp2 * sp0 :=
  fb_mul_comm (by simp) (by simp) (by simp) (by simp)

theorem sp_comm03 : (sp0 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) * sp3 = sp3 * sp0 :=
  fb_mul_comm (by simp) (by simp) (by simp) (by simp)

theorem sp_comm12 (α β : F) : (sp1 α β : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) * sp2 =
    sp2 * sp1 α β :=
  fb_mul_comm (by simp) (by simp) (by simp) (by simp)

theorem sp_comm13 (α β : F) : (sp1 α β : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) * sp3 =
    sp3 * sp1 α β :=
  fb_mul_comm (by simp) (by simp) (by simp) (by simp)

theorem sp_comm23 : (sp2 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) * sp3 = -(sp3 * sp2) :=
  fb_mul_anticomm (by simp [spX_mul_spZ]) (by simp) (by simp) (by simp [spX_mul_spZ])

theorem sp_comm10 (α β : F) : (sp1 α β : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) * sp0 =
    -(sp0 * sp1 α β) := by
  rw [sp_comm01, neg_neg]

theorem sp_comm32 : (sp3 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) * sp2 = -(sp2 * sp3) := by
  rw [sp_comm23, neg_neg]

theorem sp0_transpose : (sp0 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)ᵀ = -sp0 := by
  simp [sp0, fromBlocks_transpose, fromBlocks_neg]

theorem sp1_transpose (α β : F) :
    (sp1 α β : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)ᵀ = sp1 α β := by
  simp [sp1, fromBlocks_transpose]

theorem sp2_transpose : (sp2 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)ᵀ = sp2 := by
  simp [sp2, fromBlocks_transpose, spX_transpose]

theorem sp3_transpose : (sp3 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)ᵀ = sp3 := by
  simp [sp3, fromBlocks_transpose, spZ_transpose]

theorem symp_of_rel {ι : Type} [Fintype ι] [DecidableEq ι] {M J : Matrix ι ι F} {ε c d : F}
    (hT : Mᵀ = ε • M) (hc : M * J = c • (J * M)) (hd : M * M = d • 1) (h : ε * c * d = 1) :
    Mᵀ * J * M = J :=
  calc Mᵀ * J * M = (ε • M) * J * M := by rw [hT]
    _ = ε • (M * J * M) := by rw [Matrix.smul_mul, Matrix.smul_mul]
    _ = ε • ((c • (J * M)) * M) := by rw [hc]
    _ = (ε * c) • (J * (M * M)) := by rw [Matrix.smul_mul, Matrix.mul_assoc, smul_smul]
    _ = (ε * c * d) • J := by rw [hd, Matrix.mul_smul, Matrix.mul_one, smul_smul]
    _ = J := by rw [h, one_smul]

@[expose] def sp4Mat (α β : F) : Fin 4 → Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F :=
  ![sp0, sp1 α β, sp2, sp3]

@[expose] def sp4Sq : Fin 4 → F := ![-1, -1, 1, 1]

theorem sp4Sq_ne_zero (i : Fin 4) : (sp4Sq i : F) ≠ 0 := by
  fin_cases i <;> simp [sp4Sq]

theorem sp4_sq {α β : F} (h : α ^ 2 + β ^ 2 = -1) (i : Fin 4) :
    sp4Mat α β i * sp4Mat α β i = (sp4Sq i : F) • (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) := by
  fin_cases i
  · exact sp0_mul_sp0
  · exact sp1_mul_sp1 h
  · exact sp2_mul_sp2
  · exact sp3_mul_sp3

theorem sp_sign_zero {ι : Type} [Fintype ι] {A B : Matrix ι ι F} (h : A * B = B * A) :
    A * B = (-1 : F) ^ 0 • (B * A) := by
  rw [pow_zero, one_smul]
  exact h

theorem sp_sign_one {ι : Type} [Fintype ι] {A B : Matrix ι ι F} (h : A * B = -(B * A)) :
    A * B = (-1 : F) ^ 1 • (B * A) := by
  rw [pow_one, neg_smul, one_smul]
  exact h

theorem sp4_comm (α β : F) (i j : Fin 4) :
    sp4Mat α β i * sp4Mat α β j = (-1 : F) ^ wPauli i j • (sp4Mat α β j * sp4Mat α β i) := by
  fin_cases i <;> fin_cases j
  · exact sp_sign_zero rfl
  · exact sp_sign_one (sp_comm01 α β)
  · exact sp_sign_zero sp_comm02
  · exact sp_sign_zero sp_comm03
  · exact sp_sign_one (sp_comm10 α β)
  · exact sp_sign_zero rfl
  · exact sp_sign_zero (sp_comm12 α β)
  · exact sp_sign_zero (sp_comm13 α β)
  · exact sp_sign_zero sp_comm02.symm
  · exact sp_sign_zero (sp_comm12 α β).symm
  · exact sp_sign_zero rfl
  · exact sp_sign_one sp_comm23
  · exact sp_sign_zero sp_comm03.symm
  · exact sp_sign_zero (sp_comm13 α β).symm
  · exact sp_sign_one sp_comm32
  · exact sp_sign_zero rfl

theorem sp4_symp {α β : F} (h : α ^ 2 + β ^ 2 = -1) (i : Fin 4) :
    (sp4Mat α β i)ᵀ * sp0 * sp4Mat α β i = sp0 := by
  fin_cases i
  · exact symp_of_rel (M := sp0) (ε := -1) (c := 1) (d := -1)
      (by rw [sp0_transpose, neg_one_smul]) (by rw [one_smul]) sp0_mul_sp0 (by norm_num)
  · exact symp_of_rel (M := sp1 α β) (ε := 1) (c := -1) (d := -1)
      (by rw [sp1_transpose, one_smul]) (by rw [sp_comm10, neg_one_smul]) (sp1_mul_sp1 h)
      (by norm_num)
  · exact symp_of_rel (M := sp2) (ε := 1) (c := 1) (d := 1)
      (by rw [sp2_transpose, one_smul]) (by rw [one_smul]; exact sp_comm02.symm) sp2_mul_sp2
      (by norm_num)
  · exact symp_of_rel (M := sp3) (ε := 1) (c := 1) (d := 1)
      (by rw [sp3_transpose, one_smul]) (by rw [one_smul]; exact sp_comm03.symm) sp3_mul_sp3
      (by norm_num)

@[expose] def spUnitGL {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι F) (s : F)
    (hs : s ≠ 0) (h : M * M = s • (1 : Matrix ι ι F)) : GL ι F :=
  ⟨M, s⁻¹ • M, by rw [Matrix.mul_smul, h, smul_smul, inv_mul_cancel₀ hs, one_smul],
    by rw [Matrix.smul_mul, h, smul_smul, inv_mul_cancel₀ hs, one_smul]⟩

@[expose] def sp4GL (α β : F) (h : α ^ 2 + β ^ 2 = -1) (i : Fin 4) : GL (Fin 2 ⊕ Fin 2) F :=
  spUnitGL (sp4Mat α β i) (sp4Sq i) (sp4Sq_ne_zero i) (sp4_sq h i)

theorem exists_sq_add_sq_eq_neg_one [Finite F] (hodd : Odd (Nat.card F)) :
    ∃ α β : F, α ^ 2 + β ^ 2 = -1 := by
  have : Fintype F := Fintype.ofFinite F
  have hc : Fintype.card F % 2 = 1 := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.odd_iff.1 hodd
  obtain ⟨a, b, hab⟩ := FiniteField.exists_root_sum_quadratic (R := F)
    (f := Polynomial.X ^ 2) (g := Polynomial.X ^ 2 + Polynomial.C 1)
    (Polynomial.degree_X_pow 2) (Polynomial.degree_X_pow_add_C (by norm_num) 1) hc
  refine ⟨a, b, ?_⟩
  simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C] at hab
  linear_combination hab

theorem exists_E16_sp4 [Finite F] (hodd : Odd (Nat.card F)) :
    ∃ E : Subgroup (StatedProj (StatedSp 2 F)), (∀ x ∈ E, x ^ 2 = 1) ∧ Nat.card E = 16 := by
  obtain ⟨α, β, h⟩ := exists_sq_add_sq_eq_neg_one hodd
  have hne : (-1 : F) ≠ 1 := CFSG.GH74.GLS.neg_one_ne_one_of_odd_card F hodd
  refine exists_E16_statedProj (sp4GL α β h)
    (fun i => Subgroup.subset_closure (sp4_symp h i)) ?_ ?_ ?_
  · exact fun i => ⟨sp4Sq i, sp4_sq h i⟩
  · exact fun i j => ⟨(-1) ^ wPauli i j, sp4_comm α β i j⟩
  · exact not_scalar_of_comm_signs hne (sp4GL α β h) wPauli (fun i j => sp4_comm α β i j)
      pauli_nondeg

end Matrices

end PSp4

theorem k94_psp4 :
    K94Excl fun K _ => ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ LieModel K .PSp 2 p f := by
  refine k94Excl_of_E16 ?_
  rintro K _ _ ⟨p, f, hp, hp2, -, hL⟩
  obtain ⟨-, F, _, _, hcard, ⟨e⟩⟩ := statedClassicalModel_of_lieModel (by norm_num) hL
  have hodd : Odd (Nat.card F) := by
    rw [hcard]
    exact (hp.odd_of_ne_two hp2).pow
  exact exists_E16_of_equiv e (PSp4.exists_E16_sp4 hodd)

end CFSG.GH74.GLS.IVK.Proofs2.Ivk94
