module

public import CFSG.LocalAnalysis.SteinbergCEAnisotropicNormIsometry
public import CFSG.GroupTheory.WeirSylow.OrthogonalModels

public section

namespace CFSG.GH74.Generic.S1.Exo

open Module CFSG.GroupTheory.WeirSylow

structure OddNormPlane (K E : Type) [Field K] [Field E] [Algebra K E] where
  σ : E ≃ₐ[K] E
  finrank_eq : finrank K E = 2
  σ_ne_one : σ ≠ 1
  N : QuadraticForm K E
  algebraMap_N : ∀ z, algebraMap K E (N z) = z * σ z

namespace OddNormPlane

variable {K E : Type} [Field K] [Finite K] [Field E] [Algebra K E] (D : OddNormPlane K E)

include D

theorem sigma_eq_pow (z : E) : D.σ z = z ^ Nat.card K := by
  classical
  have := Fintype.ofFinite K
  rw [Nat.card_eq_fintype_card]
  exact CFSG.LocalAnalysis.eq_pow_card_of_ne_one D.finrank_eq D.σ_ne_one z

theorem card_E : Nat.card E = Nat.card K ^ 2 := by
  classical
  have := Fintype.ofFinite K
  rw [Nat.card_eq_fintype_card (α := K)]
  exact CFSG.LocalAnalysis.natCard_eq_sq_of_finrank_eq_two D.finrank_eq

omit [Finite K] in
theorem moduleFinite : Module.Finite K E :=
  Module.finite_of_finrank_pos (by rw [D.finrank_eq]; omega)

theorem finite_E : Finite E := by
  have := D.moduleFinite
  exact Module.finite_of_finite K

theorem sigma_sigma (z : E) : D.σ (D.σ z) = z := by
  classical
  have := D.finite_E
  have := Fintype.ofFinite E
  rw [D.sigma_eq_pow, D.sigma_eq_pow, ← pow_mul, ← sq, ← D.card_E, Nat.card_eq_fintype_card]
  exact FiniteField.pow_card z

theorem sigma_eq_self_iff (z : E) : D.σ z = z ↔ z ∈ (algebraMap K E).range := by
  classical
  have := Fintype.ofFinite K
  rw [D.sigma_eq_pow, Nat.card_eq_fintype_card]
  exact CFSG.LocalAnalysis.pow_card_eq_self_iff D.finrank_eq z

omit [Finite K] in
theorem eq_zero_of_N_eq_zero {z : E} (h : D.N z = 0) : z = 0 := by
  have h1 := D.algebraMap_N z
  rw [h, map_zero] at h1
  rcases mul_eq_zero.mp h1.symm with h2 | h2
  · exact h2
  · exact (map_eq_zero_iff D.σ D.σ.injective).mp h2

end OddNormPlane

section Existence

variable {K : Type} [Field K] {b c : K}

@[expose] def qaStar : QuadraticAlgebra K (-c) b ≃ₐ[K] QuadraticAlgebra K (-c) b where
  toFun := star
  invFun := star
  left_inv := star_star
  right_inv := star_star
  map_mul' x y := by rw [star_mul, mul_comm]
  map_add' := star_add
  commutes' r := by
    ext <;> simp [QuadraticAlgebra.re_star, QuadraticAlgebra.im_star]

theorem qaStar_apply (z : QuadraticAlgebra K (-c) b) : qaStar z = star z :=
  rfl

@[expose] noncomputable def qaNormForm (b c : K) : QuadraticForm K (QuadraticAlgebra K (-c) b) :=
  (binForm b c).comp (qaEquiv b c).toLinearMap

theorem qaNormForm_apply (z : QuadraticAlgebra K (-c) b) :
    qaNormForm b c z = QuadraticAlgebra.norm z := by
  rw [qaNormForm, QuadraticMap.comp_apply]
  exact binForm_qaEquiv z

@[expose] noncomputable def oddNormPlaneOfBin [Fact (∀ r : K, r ^ 2 ≠ -c + b * r)]
    (h2 : (2 : K) ≠ 0) : OddNormPlane K (QuadraticAlgebra K (-c) b) where
  σ := qaStar
  finrank_eq := by
    rw [(qaEquiv b c).finrank_eq]
    simp
  σ_ne_one := fun h => h2 (by
    have := congrArg (fun φ : QuadraticAlgebra K (-c) b ≃ₐ[K] QuadraticAlgebra K (-c) b =>
      (φ (⟨0, 1⟩ : QuadraticAlgebra K (-c) b)).im) h
    simp [qaStar_apply] at this
    linear_combination -this)
  N := qaNormForm b c
  algebraMap_N z := by
    rw [qaNormForm_apply, QuadraticAlgebra.algebraMap_norm_eq_mul_star]
    rfl

theorem exists_oddNormPlane (K : Type) [Field K] [Finite K] (h2 : (2 : K) ≠ 0) :
    ∃ (E : Type) (_ : Field E) (_ : Algebra K E), Nonempty (OddNormPlane K E) := by
  have hchar : ringChar K ≠ 2 := fun h => h2 (by
    have := (ringChar.spec K 2).2 (h ▸ dvd_refl _)
    exact_mod_cast this)
  obtain ⟨a, ha⟩ := FiniteField.exists_nonsquare hchar
  have hirr : ∀ s : K, s ^ 2 + 0 * s + (-a) ≠ 0 := fun s hs =>
    ha ⟨s, by linear_combination -hs⟩
  have : Fact (∀ r : K, r ^ 2 ≠ -(-a) + 0 * r) := ⟨noRoot_quadraticAlgebra hirr⟩
  exact ⟨QuadraticAlgebra K (-(-a)) 0, inferInstance, inferInstance, ⟨oddNormPlaneOfBin h2⟩⟩

end Existence

end CFSG.GH74.Generic.S1.Exo
