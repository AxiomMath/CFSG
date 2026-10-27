module

public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Pairs
public import TauCeti.LinearAlgebra.BilinearForm.Orthogonal
public import TauCeti.LinearAlgebra.BilinearForm.SymplecticBasis

public section

namespace CFSG.ClassicalInvolution.Models.SymplecticPairs

open Matrix CFSG.Assembly.LowTwoRank
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open scoped MatrixGroups

variable {K : Type} [Field K] {n m : ℕ}

section Gram

theorem toBilin'_J_apply (u v : Fin n ⊕ Fin n → K) :
    Matrix.toBilin' (Matrix.J (Fin n) K) u v = -form u v := by
  rw [Matrix.toBilin'_apply', form, gram_eq_neg_J, Matrix.neg_mulVec, dotProduct_neg, neg_neg]

theorem form_self (u : Fin n ⊕ Fin n → K) : form u u = 0 := by
  rw [form_apply, Fintype.sum_sum_type]
  simp only [par_inl, par_inr, sgn_inl, sgn_inr]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_eq_zero fun i _ => by ring

end Gram

section Basis

theorem isAlt_toBilin'_J : (Matrix.toBilin' (Matrix.J (Fin n) K)).IsAlt := fun v => by
  rw [toBilin'_J_apply, form_self, neg_zero]

theorem nondegenerate_toBilin'_J : (Matrix.toBilin' (Matrix.J (Fin n) K)).Nondegenerate :=
  Matrix.nondegenerate_toBilin'_iff.2 (Matrix.nondegenerate_iff_det_ne_zero.2
    (Matrix.isUnit_det_J _ _).ne_zero)

theorem exists_symplectic_basis_pair {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {B : LinearMap.BilinForm K V} (hAlt : B.IsAlt)
    (hnd : B.Nondegenerate) {e f : V} (hfe : B f e = 1) :
    ∃ (m : ℕ) (b : Module.Basis (Fin (m + 1) ⊕ Fin (m + 1)) K V),
      (∀ x y, B (b x) (b y) = Matrix.J (Fin (m + 1)) K x y) ∧ b (Sum.inl 0) = e ∧
        b (Sum.inr 0) = f := by
  have hZ : (B.restrict (B.orthogonal (Submodule.span K {e, f}))).IsAlt := fun z => hAlt z
  obtain ⟨m', c, hc⟩ := hZ.exists_basis_toMatrix_eq_J
    (hAlt.restrict_nondegenerate_orthogonal_span_pair hfe hnd)
  have hc' : ∀ x y, B (c x) (c y) = Matrix.J (Fin m') K x y := fun x y => by
    rw [← hc, LinearMap.BilinForm.toMatrix_apply, LinearMap.BilinForm.restrict_apply,
      LinearMap.domRestrict_apply]
  obtain ⟨b, hb, hbd⟩ := hAlt.exists_basis_apply_eq_J_of_basis_orthogonal_span_pair hnd hfe c hc'
  exact ⟨m', b, hb, by rw [hbd]; simp, by rw [hbd]; simp⟩

theorem exists_symplectic_basis (u w : Fin (m + 1) ⊕ Fin (m + 1) → K) (h : form u w = 1) :
    ∃ b : Module.Basis (Fin (m + 1) ⊕ Fin (m + 1)) K (Fin (m + 1) ⊕ Fin (m + 1) → K),
      (∀ x y, form (b x) (b y) = gram K (m + 1) x y) ∧ b (Sum.inl 0) = u ∧
        b (Sum.inr 0) = w := by
  set B := Matrix.toBilin' (Matrix.J (Fin (m + 1)) K) with hB
  have hfe : B w u = 1 := by
    rw [hB, toBilin'_J_apply, form_antisymm, neg_neg]
    exact h
  obtain ⟨m', b, hb, hbu, hbw⟩ :=
    exists_symplectic_basis_pair (isAlt_toBilin'_J (n := m + 1)) nondegenerate_toBilin'_J hfe
  have hm' : m' = m := by
    have := Module.finrank_eq_card_basis b
    rw [Module.finrank_pi] at this
    simp only [Fintype.card_sum, Fintype.card_fin] at this
    omega
  subst hm'
  refine ⟨b, fun x y => ?_, hbu, hbw⟩
  have := hb x y
  rw [hB, toBilin'_J_apply] at this
  rw [gram_eq_neg_J, Matrix.neg_apply, ← this, neg_neg]

theorem exists_symplectic_basis_two (u₁ w₁ u₂ w₂ : Fin (m + 1 + 1) ⊕ Fin (m + 1 + 1) → K)
    (h₁ : form u₁ w₁ = 1) (h₂ : form u₂ w₂ = 1) (o₁ : form u₁ u₂ = 0) (o₂ : form u₁ w₂ = 0)
    (o₃ : form w₁ u₂ = 0) (o₄ : form w₁ w₂ = 0) :
    ∃ b : Module.Basis (Fin (m + 1 + 1) ⊕ Fin (m + 1 + 1)) K
        (Fin (m + 1 + 1) ⊕ Fin (m + 1 + 1) → K),
      (∀ x y, form (b x) (b y) = gram K (m + 1 + 1) x y) ∧ b (Sum.inl 0) = u₁ ∧
        b (Sum.inr 0) = w₁ ∧ b (Sum.inl 1) = u₂ ∧ b (Sum.inr 1) = w₂ := by
  set B := Matrix.toBilin' (Matrix.J (Fin (m + 1 + 1)) K) with hB
  have hAlt : B.IsAlt := isAlt_toBilin'_J
  have hnd : B.Nondegenerate := nondegenerate_toBilin'_J
  have hB' : ∀ u v, B u v = -form u v := fun u v => toBilin'_J_apply u v
  have hfe₁ : B w₁ u₁ = 1 := by
    rw [hB', form_antisymm, neg_neg]
    exact h₁
  have he₂ : u₂ ∈ B.orthogonal (Submodule.span K {u₁, w₁}) := by
    rw [LinearMap.BilinForm.mem_orthogonal_span_pair_iff]
    refine ⟨?_, ?_⟩
    · rw [hB', o₁, neg_zero]
    · rw [hB', o₃, neg_zero]
  have hf₂ : w₂ ∈ B.orthogonal (Submodule.span K {u₁, w₁}) := by
    rw [LinearMap.BilinForm.mem_orthogonal_span_pair_iff]
    refine ⟨?_, ?_⟩
    · rw [hB', o₂, neg_zero]
    · rw [hB', o₄, neg_zero]
  have hZ : (B.restrict (B.orthogonal (Submodule.span K {u₁, w₁}))).IsAlt := fun z => hAlt z
  have hZnd := hAlt.restrict_nondegenerate_orthogonal_span_pair hfe₁ hnd
  have hfe₂ : (B.restrict (B.orthogonal (Submodule.span K {u₁, w₁})))
      (⟨w₂, hf₂⟩ : B.orthogonal (Submodule.span K {u₁, w₁})) ⟨u₂, he₂⟩ = 1 := by
    rw [LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply]
    simp only [hB']
    rw [form_antisymm, neg_neg]
    exact h₂
  obtain ⟨m', c, hc, hcl, hcr⟩ := exists_symplectic_basis_pair hZ hZnd hfe₂
  have hc' : ∀ x y, B (c x) (c y) = Matrix.J (Fin (m' + 1)) K x y := fun x y => by
    rw [← hc x y, LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply]
  obtain ⟨b, hb, hbd⟩ := hAlt.exists_basis_apply_eq_J_of_basis_orthogonal_span_pair hnd hfe₁ c hc'
  have hm' : m' = m := by
    have h1 := Module.finrank_eq_card_basis b
    rw [Module.finrank_pi] at h1
    simp only [Fintype.card_sum, Fintype.card_fin] at h1
    omega
  subst hm'
  refine ⟨b, fun x y => ?_, by rw [hbd]; simp, by rw [hbd]; simp, ?_, ?_⟩
  · have := hb x y
    rw [hB, toBilin'_J_apply] at this
    rw [gram_eq_neg_J, Matrix.neg_apply, ← this, neg_neg]
  · rw [hbd]
    have : (1 : Fin (m' + 1 + 1)) = Fin.succ 0 := rfl
    rw [this, Sum.elim_inl, Fin.cons_succ, hcl]
  · rw [hbd]
    have : (1 : Fin (m' + 1 + 1)) = Fin.succ 0 := rfl
    rw [this, Sum.elim_inr, Fin.cons_succ, hcr]

variable (b : Module.Basis (Fin n ⊕ Fin n) K (Fin n ⊕ Fin n → K))

@[expose] noncomputable def basisMat : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K :=
  Matrix.of fun r c => b c r

theorem basisMat_symplectic (hb : ∀ x y, form (b x) (b y) = gram K n x y) :
    (basisMat b)ᵀ * gram K n * basisMat b = gram K n := by
  ext x y
  rw [transpose_mul_gram_mul_apply, ← hb x y, form_apply]
  rfl

@[expose] noncomputable def ofSymplecticBasis
    (hb : ∀ x y, form (b x) (b y) = gram K n x y) : StatedSp n K :=
  ofSymplecticMat (basisMat b) (basisMat_symplectic b hb)

theorem mat_ofSymplecticBasis (hb : ∀ x y, form (b x) (b y) = gram K n x y) :
    mat n K (ofSymplecticBasis b hb) = basisMat b := rfl

theorem mat_ofSymplecticBasis_mulVec_single (hb : ∀ x y, form (b x) (b y) = gram K n x y)
    (x : Fin n ⊕ Fin n) : mat n K (ofSymplecticBasis b hb) *ᵥ Pi.single x 1 = b x := by
  rw [mat_ofSymplecticBasis, Matrix.mulVec_single_one]
  rfl

end Basis

section Transitivity

theorem exists_sp_apply_eq (u w : Fin (m + 1) ⊕ Fin (m + 1) → K) (h : form u w = 1) :
    ∃ g : StatedSp (m + 1) K, mat (m + 1) K g *ᵥ Pi.single (Sum.inl 0) 1 = u ∧
      mat (m + 1) K g *ᵥ Pi.single (Sum.inr 0) 1 = w := by
  have h0 : form (Pi.single (Sum.inl 0) (1 : K) : Fin (m + 1) ⊕ Fin (m + 1) → K)
      (Pi.single (Sum.inr 0) 1) = 1 := by
    rw [form_single_right]
    simp
  obtain ⟨b₁, hb₁, h1u, h1w⟩ := exists_symplectic_basis _ _ h0
  obtain ⟨b₂, hb₂, h2u, h2w⟩ := exists_symplectic_basis u w h
  have e1 : mat (m + 1) K (ofSymplecticBasis b₁ hb₁) *ᵥ Pi.single (Sum.inl 0) 1 =
      Pi.single (Sum.inl 0) 1 := by
    rw [mat_ofSymplecticBasis_mulVec_single, h1u]
  have e2 : mat (m + 1) K (ofSymplecticBasis b₁ hb₁) *ᵥ Pi.single (Sum.inr 0) 1 =
      Pi.single (Sum.inr 0) 1 := by
    rw [mat_ofSymplecticBasis_mulVec_single, h1w]
  refine ⟨ofSymplecticBasis b₂ hb₂ * (ofSymplecticBasis b₁ hb₁)⁻¹, ?_, ?_⟩
  · rw [map_mul, ← Matrix.mulVec_mulVec, ← (mulVec_eq_iff _ _ _).1 e1,
      mat_ofSymplecticBasis_mulVec_single, h2u]
  · rw [map_mul, ← Matrix.mulVec_mulVec, ← (mulVec_eq_iff _ _ _).1 e2,
      mat_ofSymplecticBasis_mulVec_single, h2w]

theorem mulVec_inv_eq_self {g : StatedSp n K} {v : Fin n ⊕ Fin n → K}
    (h : mat n K g *ᵥ v = v) : mat n K g⁻¹ *ᵥ v = v :=
  ((mulVec_eq_iff g v v).1 h).symm

theorem exists_sp_apply_eq_two (u₁ w₁ u₂ w₂ : Fin (m + 1 + 1) ⊕ Fin (m + 1 + 1) → K)
    (h₁ : form u₁ w₁ = 1) (h₂ : form u₂ w₂ = 1) (o₁ : form u₁ u₂ = 0) (o₂ : form u₁ w₂ = 0)
    (o₃ : form w₁ u₂ = 0) (o₄ : form w₁ w₂ = 0) :
    ∃ g : StatedSp (m + 1 + 1) K,
      mat _ K g *ᵥ Pi.single (Sum.inl 0) 1 = u₁ ∧ mat _ K g *ᵥ Pi.single (Sum.inr 0) 1 = w₁ ∧
        mat _ K g *ᵥ Pi.single (Sum.inl 1) 1 = u₂ ∧ mat _ K g *ᵥ Pi.single (Sum.inr 1) 1 = w₂ := by
  set e₁ : Fin (m + 1 + 1) ⊕ Fin (m + 1 + 1) → K := Pi.single (Sum.inl 0) 1 with he₁
  set f₁ : Fin (m + 1 + 1) ⊕ Fin (m + 1 + 1) → K := Pi.single (Sum.inr 0) 1 with hf₁
  set e₂ : Fin (m + 1 + 1) ⊕ Fin (m + 1 + 1) → K := Pi.single (Sum.inl 1) 1 with he₂
  set f₂ : Fin (m + 1 + 1) ⊕ Fin (m + 1 + 1) → K := Pi.single (Sum.inr 1) 1 with hf₂
  have s₁ : form e₁ f₁ = 1 := by rw [he₁, hf₁, form_single_right]; simp
  have s₂ : form e₂ f₂ = 1 := by rw [he₂, hf₂, form_single_right]; simp
  have s₃ : form e₁ e₂ = 0 := by rw [he₁, he₂, form_single_right]; simp
  have s₄ : form e₁ f₂ = 0 := by rw [he₁, hf₂, form_single_right]; simp
  have s₅ : form f₁ e₂ = 0 := by rw [hf₁, he₂, form_single_right]; simp
  have s₆ : form f₁ f₂ = 0 := by rw [hf₁, hf₂, form_single_right]; simp
  obtain ⟨b₁, hb₁, h1a, h1b, h1c, h1d⟩ := exists_symplectic_basis_two e₁ f₁ e₂ f₂ s₁ s₂ s₃ s₄ s₅ s₆
  obtain ⟨b₂, hb₂, h2a, h2b, h2c, h2d⟩ := exists_symplectic_basis_two u₁ w₁ u₂ w₂ h₁ h₂ o₁ o₂ o₃ o₄
  have key : ∀ (x : Fin (m + 1 + 1) ⊕ Fin (m + 1 + 1)), b₁ x = Pi.single x 1 →
      mat _ K (ofSymplecticBasis b₂ hb₂ * (ofSymplecticBasis b₁ hb₁)⁻¹) *ᵥ Pi.single x 1 =
        b₂ x := fun x hx => by
    have e1 : mat _ K (ofSymplecticBasis b₁ hb₁) *ᵥ Pi.single x 1 = Pi.single x 1 := by
      rw [mat_ofSymplecticBasis_mulVec_single, hx]
    rw [map_mul, ← Matrix.mulVec_mulVec, mulVec_inv_eq_self e1,
      mat_ofSymplecticBasis_mulVec_single]
  refine ⟨ofSymplecticBasis b₂ hb₂ * (ofSymplecticBasis b₁ hb₁)⁻¹, ?_, ?_, ?_, ?_⟩
  · rw [key _ h1a, h2a]
  · rw [key _ h1b, h2b]
  · rw [key _ h1c, h2c]
  · rw [key _ h1d, h2d]

end Transitivity

end CFSG.ClassicalInvolution.Models.SymplecticPairs
