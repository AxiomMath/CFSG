module

public import CFSG.GF2Type.Smith1979.CaseIIASp
public import TauCeti.LinearAlgebra.BilinearForm.SymplecticBasis

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.Case2.Sp

open Module Matrix

theorem zmod2_neg (a : ZMod 2) : -a = a := by
  have : ∀ a : ZMod 2, -a = a := by decide
  exact this a

theorem sum_inl_inr_eq_trace {m : ℕ} (Y : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) (ZMod 2)) :
    ∑ i : Fin m, (Y + Yᵀ) (Sum.inl i) (Sum.inr i) =
      Matrix.trace (Matrix.J (Fin m) (ZMod 2) * Y) := by
  classical
  rw [Matrix.trace, Fintype.sum_sum_type]
  simp only [Matrix.diag_apply, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.J,
    Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
    Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, zero_mul, Finset.sum_const_zero, zero_add,
    Matrix.neg_apply, Matrix.one_apply, neg_mul, Matrix.add_apply, Matrix.transpose_apply,
    ite_mul, one_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_neg_distrib,
    add_zero]
  rw [Finset.sum_add_distrib, zmod2_neg, add_comm]

theorem exists_add_transpose {κ : Type*} [Fintype κ] (e : κ ≃ Fin (Fintype.card κ))
    (G : Matrix κ κ (ZMod 2)) (hsymm : ∀ x y, G x y = G y x) (hdiag : ∀ x, G x x = 0) :
    ∃ Y : Matrix κ κ (ZMod 2), Y + Yᵀ = G := by
  classical
  refine ⟨Matrix.of fun x y => if e x < e y then G x y else 0, ?_⟩
  ext x y
  simp only [Matrix.add_apply, Matrix.of_apply, Matrix.transpose_apply]
  rcases lt_trichotomy (e x) (e y) with h | h | h
  · rw [if_pos h, if_neg (not_lt.mpr h.le), add_zero]
  · have hxy : x = y := e.injective h
    subst hxy
    simp [hdiag]
  · rw [if_neg (not_lt.mpr h.le), if_pos h, zero_add, hsymm]

section HalfTrace

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]

theorem exists_halfTrace {ω : LinearMap.BilinForm (ZMod 2) W} (halt : ∀ u, ω u u = 0)
    (hnd : ω.Nondegenerate) (h6 : finrank (ZMod 2) W = 6) :
    ∃ τ : LinearMap.BilinForm (ZMod 2) W → ZMod 2,
      (∀ B B', τ (B + B') = τ B + τ B') ∧ τ ω = 1 ∧
      ∀ γ : W ≃ₗ[ZMod 2] W, (∀ u v, ω (γ u) (γ v) = ω u v) →
        ∀ B : LinearMap.BilinForm (ZMod 2) W, (∀ u, B u u = 0) →
          τ (B.compl₁₂ (γ : W →ₗ[ZMod 2] W) (γ : W →ₗ[ZMod 2] W)) = τ B := by
  classical
  have hIsAlt : ω.IsAlt := fun u => halt u
  obtain ⟨m, b, hb⟩ := hIsAlt.exists_basis_toMatrix_eq_J hnd
  have hcard : Fintype.card (Fin m ⊕ Fin m) = 6 := by
    rw [← h6, Module.finrank_eq_card_basis b]
  have hm : m = 3 := by
    rw [Fintype.card_sum, Fintype.card_fin] at hcard
    omega
  have hJ : ∀ x y, ω (b x) (b y) = Matrix.J (Fin m) (ZMod 2) x y := fun x y => by
    rw [← hb, LinearMap.BilinForm.toMatrix_apply]
  refine ⟨fun B => ∑ i : Fin m, B (b (Sum.inl i)) (b (Sum.inr i)), ?_, ?_, ?_⟩
  · intro B B'
    simp [Finset.sum_add_distrib]
  · have : ∀ i : Fin m, ω (b (Sum.inl i)) (b (Sum.inr i)) = 1 := fun i => by
      rw [hJ]
      simp [Matrix.J, zmod2_neg]
    simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    subst hm
    decide
  · intro γ hγ B hB
    set M : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) (ZMod 2) :=
      LinearMap.toMatrix b b (γ : W →ₗ[ZMod 2] W) with hM
    set G : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) (ZMod 2) :=
      LinearMap.BilinForm.toMatrix b B with hG
    have hGγ : LinearMap.BilinForm.toMatrix b (B.compl₁₂ (γ : W →ₗ[ZMod 2] W)
        (γ : W →ₗ[ZMod 2] W)) = Mᵀ * G * M :=
      LinearMap.BilinForm.toMatrix_comp b b B (γ : W →ₗ[ZMod 2] W) (γ : W →ₗ[ZMod 2] W)
    have hωγ : ω.comp (γ : W →ₗ[ZMod 2] W) (γ : W →ₗ[ZMod 2] W) = ω :=
      LinearMap.ext fun u => LinearMap.ext fun v => hγ u v
    have hMJ : Mᵀ * Matrix.J (Fin m) (ZMod 2) * M = Matrix.J (Fin m) (ZMod 2) := by
      have h1 := LinearMap.BilinForm.toMatrix_comp b b ω (γ : W →ₗ[ZMod 2] W)
        (γ : W →ₗ[ZMod 2] W)
      rw [hωγ, hb] at h1
      exact h1.symm
    have hMsp : M ∈ Matrix.symplecticGroup (Fin m) (ZMod 2) :=
      SymplecticGroup.mem_iff'.mpr hMJ
    have hMJM : M * Matrix.J (Fin m) (ZMod 2) * Mᵀ = Matrix.J (Fin m) (ZMod 2) :=
      SymplecticGroup.mem_iff.mp hMsp
    have hGs : ∀ x y, G x y = G y x := fun x y => by
      rw [hG, LinearMap.BilinForm.toMatrix_apply, LinearMap.BilinForm.toMatrix_apply]
      exact alt_symm B hB _ _
    have hGd : ∀ x, G x x = 0 := fun x => by
      rw [hG, LinearMap.BilinForm.toMatrix_apply]
      exact hB _
    obtain ⟨Y, hY⟩ := exists_add_transpose (Fintype.equivFin (Fin m ⊕ Fin m)) G hGs hGd
    have h1 : ∑ i : Fin m, B (b (Sum.inl i)) (b (Sum.inr i)) =
        Matrix.trace (Matrix.J (Fin m) (ZMod 2) * Y) := by
      rw [← sum_inl_inr_eq_trace, hY]
      simp [hG]
    have h2 : ∑ i : Fin m, (B.compl₁₂ (γ : W →ₗ[ZMod 2] W) (γ : W →ₗ[ZMod 2] W))
        (b (Sum.inl i)) (b (Sum.inr i)) =
        Matrix.trace (Matrix.J (Fin m) (ZMod 2) * (Mᵀ * Y * M)) := by
      rw [← sum_inl_inr_eq_trace]
      have : Mᵀ * Y * M + (Mᵀ * Y * M)ᵀ = Mᵀ * G * M := by
        rw [← hY, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose]
        simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
      rw [this, ← hGγ]
      simp
    simp only
    rw [h1, h2]
    calc Matrix.trace (Matrix.J (Fin m) (ZMod 2) * (Mᵀ * Y * M))
        = Matrix.trace (M * (Matrix.J (Fin m) (ZMod 2) * (Mᵀ * Y))) := by
          rw [← Matrix.mul_assoc, Matrix.trace_mul_comm]
      _ = Matrix.trace (M * Matrix.J (Fin m) (ZMod 2) * Mᵀ * Y) := by
          simp only [Matrix.mul_assoc]
      _ = Matrix.trace (Matrix.J (Fin m) (ZMod 2) * Y) := by rw [hMJM]


end HalfTrace

section FElementary

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
variable {ω : LinearMap.BilinForm (ZMod 2) W} {V : Submodule (ZMod 2) W}

namespace IsF

variable (D : SpData ω V) {x y : W ≃ₗ[ZMod 2] W} (hx : IsF ω V x) (hy : IsF ω V y)
include D hx hy

theorem mul_comm' : x * y = y * x := by
  refine LinearEquiv.ext fun u => ?_
  have h1 := hx.mul_sub D hy u
  have h2 := hy.mul_sub D hx u
  have h3 : (x * y) u - u = (y * x) u - u := by rw [h1, h2, add_comm]
  exact sub_left_injective h3

end IsF

theorem IsF.mul_self' (D : SpData ω V) {x : W ≃ₗ[ZMod 2] W} (hx : IsF ω V x) : x * x = 1 := by
  refine LinearEquiv.ext fun u => ?_
  have h1 := hx.mul_sub D hx u
  rw [vec_add_self] at h1
  have h2 : (x * x) u - u = 0 := h1
  exact sub_eq_zero.mp h2

end FElementary

end CFSG.GF2Type.Smith1979.Case2.Sp
