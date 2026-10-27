module

public import CFSG.Open.StatedDefs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.LinearAlgebra.Matrix.Transvection

public section

namespace CFSG.ClassicalGroups.SpecialLinear

open Matrix

private theorem nat_transvection_mulVec {K : Type*} [Field K] {n : ℕ} (a b : Fin n) (c : K)
    (x : Fin n → K) :
    Matrix.transvection a b c *ᵥ x = x + Pi.single a (c * x b) := by
  funext i
  rw [Matrix.transvection, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec]
  by_cases hi : i = a
  · subst hi
    simp [Function.update_apply, Pi.single_apply]
  · simp [Function.update_apply, Pi.single_apply, hi]

private theorem nat_transvection_transpose {K : Type*} [Field K] {n : ℕ} (a b : Fin n) (c : K) :
    (Matrix.transvection a b c)ᵀ = Matrix.transvection b a c := by
  simp only [Matrix.transvection, Matrix.transpose_add, Matrix.transpose_one,
    Matrix.transpose_single]

private theorem nat_transvection_mul_neg {K : Type*} [Field K] {n : ℕ} {a b : Fin n} (hab : a ≠ b) :
    Matrix.transvection a b (1 : K) * Matrix.transvection a b (-1 : K) = 1 := by
  rw [Matrix.transvection_mul_transvection_same a b hab]
  simp

private theorem nat_not_dual_of_transvections {K : Type*} [Field K] {n : ℕ}
    (f : (Fin n → K) →+ (Fin n → K)) (hinj : Function.Injective f)
    (p j₁ j₂ : Fin n) (h₁ : p ≠ j₁) (h₂ : p ≠ j₂) (h₁₂ : j₁ ≠ j₂)
    (H : ∀ a b : Fin n, a ≠ b → ∀ x : Fin n → K,
      f (Matrix.transvection a b (1 : K) *ᵥ x) = (Matrix.transvection a b (-1 : K))ᵀ *ᵥ f x) :
    False := by
  have key : ∀ a b : Fin n, a ≠ b →
      f (Pi.single a 1) = Pi.single b (-(f (Pi.single b 1) a)) := by
    intro a b hab
    have h := H a b hab (Pi.single b 1)
    rw [nat_transvection_transpose] at h
    simp only [nat_transvection_mulVec, one_mul, Pi.single_eq_same, neg_one_mul,
      map_add] at h
    exact add_left_cancel h
  have hv2 : f (Pi.single p 1) j₂ = 0 := by
    rw [key p j₁ h₁]
    simp [Pi.single_apply, Ne.symm h₁₂]
  have hc2 : f (Pi.single j₂ 1) p = 0 := by
    have h := congrFun (key p j₂ h₂) j₂
    rw [hv2, Pi.single_eq_same] at h
    exact neg_eq_zero.mp h.symm
  have hv : f (Pi.single p 1) = 0 := by
    rw [key p j₂ h₂, hc2, neg_zero, Pi.single_zero]
  have hp : (Pi.single p (1 : K) : Fin n → K) = 0 := by
    apply hinj
    rw [hv, map_zero]
  have h := congrFun hp p
  simp at h

theorem not_exists_natural_dual_hom {K : Type*} [Field K] {n : ℕ} (hn : 3 ≤ n) :
    ¬ ∃ f : (Fin n → K) →+ (Fin n → K), Function.Injective f ∧
      ∀ (g : Matrix.SpecialLinearGroup (Fin n) K) (x : Fin n → K),
        f ((g : Matrix (Fin n) (Fin n) K) *ᵥ x) =
          ((g⁻¹ : Matrix.SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ *ᵥ f x := by
  rintro ⟨f, hinj, hf⟩
  have H : ∀ a b : Fin n, a ≠ b → ∀ x : Fin n → K,
      f (Matrix.transvection a b (1 : K) *ᵥ x) = (Matrix.transvection a b (-1 : K))ᵀ *ᵥ f x := by
    intro a b hab x
    have hdetA : (Matrix.transvection a b (1 : K)).det = 1 :=
      Matrix.det_transvection_of_ne a b hab 1
    obtain ⟨g, hg⟩ : ∃ g : Matrix.SpecialLinearGroup (Fin n) K,
        (g : Matrix (Fin n) (Fin n) K) = Matrix.transvection a b (1 : K) :=
      ⟨⟨Matrix.transvection a b (1 : K), hdetA⟩, rfl⟩
    have h1 : ((g⁻¹ : Matrix.SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        (g : Matrix (Fin n) (Fin n) K) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
    have h2 : (g : Matrix (Fin n) (Fin n) K) * Matrix.transvection a b (-1 : K) = 1 := by
      rw [hg]
      exact nat_transvection_mul_neg (K := K) hab
    have hinvM : ((g⁻¹ : Matrix.SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        Matrix.transvection a b (-1 : K) := by
      calc ((g⁻¹ : Matrix.SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K)
          = ((g⁻¹ : Matrix.SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *
              ((g : Matrix (Fin n) (Fin n) K) * Matrix.transvection a b (-1 : K)) := by
            rw [h2, mul_one]
        _ = (((g⁻¹ : Matrix.SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *
              (g : Matrix (Fin n) (Fin n) K)) * Matrix.transvection a b (-1 : K) := by
            rw [Matrix.mul_assoc]
        _ = Matrix.transvection a b (-1 : K) := by
            rw [h1, one_mul]
    have h := hf g x
    rw [hinvM, hg] at h
    exact h
  exact nat_not_dual_of_transvections f hinj ⟨0, by omega⟩ ⟨1, by omega⟩ ⟨2, by omega⟩
    (by simp) (by simp) (by simp) H

theorem not_exists_natural_dual_hom_statedSL {K : Type} [Field K] {n : ℕ} (hn : 3 ≤ n) :
    ¬ ∃ f : (Fin n → K) →+ (Fin n → K), Function.Injective f ∧
      ∀ (g : GL (Fin n) K), g ∈ CFSG.Open.StatedSL n K → ∀ (x : Fin n → K),
        f ((g : Matrix (Fin n) (Fin n) K) *ᵥ x) =
          ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ *ᵥ f x := by
  rintro ⟨f, hinj, hf⟩
  refine not_exists_natural_dual_hom hn ⟨f, hinj, fun g x => ?_⟩
  have hmem : Matrix.SpecialLinearGroup.toGL g ∈ CFSG.Open.StatedSL n K :=
    Subgroup.subset_closure g.prop
  exact hf _ hmem x

end CFSG.ClassicalGroups.SpecialLinear

end
