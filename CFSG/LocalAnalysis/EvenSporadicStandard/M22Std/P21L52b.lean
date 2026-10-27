module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.P21L52a
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismGeneration

public section

namespace CFSG.EvenSporadicStandard.M22Std.P21L52

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

@[expose] def x₀ : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  !![0, 1, 1, 0, 1; 1, 1, 0, 1, 0; 1, 0, 1, 0, 0; 0, 1, 0, 0, 0; 1, 0, 0, 0, 0]

set_option maxRecDepth 100000 in
theorem x₀_pow : x₀ ^ 31 = 1 := by decide +revert

theorem x₀_transpose : x₀.transpose = x₀ := by decide

theorem x₀_ne_one : x₀ ≠ 1 := by decide

set_option maxRecDepth 100000 in
theorem x₀_det : x₀.det = 1 := by decide

variable {K : Type} [Field K] [Finite K]

theorem exists_symm_order_31 (hK : Nat.card K = 2) :
    ∃ x : SpecialLinearGroup (Fin 5) K, x ^ 31 = 1 ∧ x ≠ 1 ∧ (x⁻¹).transpose = x⁻¹ := by
  have : Fintype K := Fintype.ofFinite K
  let ε : K ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, hK, ZMod.card])
  let f : ZMod 2 →+* K := (ε.symm : ZMod 2 ≃+* K).toRingHom
  have hdet : (f.mapMatrix x₀).det = 1 := by
    rw [← RingHom.map_det, x₀_det, map_one]
  let X : SpecialLinearGroup (Fin 5) K := ⟨f.mapMatrix x₀, hdet⟩
  have hXc : (X : Matrix (Fin 5) (Fin 5) K) = f.mapMatrix x₀ := rfl
  refine ⟨X, ?_, ?_, ?_⟩
  · have h : ((X ^ 31 : SpecialLinearGroup (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) =
        ((1 : SpecialLinearGroup (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) := by
      rw [Matrix.SpecialLinearGroup.coe_pow, hXc, ← map_pow, x₀_pow, map_one,
        Matrix.SpecialLinearGroup.coe_one]
    exact Matrix.SpecialLinearGroup.ext _ _ (fun i j => congrFun (congrFun h i) j)
  · intro h
    have h1 := congrArg (fun g : SpecialLinearGroup (Fin 5) K => (g : Matrix (Fin 5) (Fin 5) K)) h
    simp only [hXc, Matrix.SpecialLinearGroup.coe_one] at h1
    have : f.mapMatrix x₀ = f.mapMatrix 1 := by rw [map_one]; exact h1
    exact x₀_ne_one (Matrix.map_injective f.injective this)
  · have hsym : (f.mapMatrix x₀)ᵀ = f.mapMatrix x₀ := by
      rw [RingHom.mapMatrix_apply, ← Matrix.transpose_map, x₀_transpose]
    have h : (((X⁻¹).transpose : SpecialLinearGroup (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) =
        ((X⁻¹ : SpecialLinearGroup (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) := by
      rw [Matrix.SpecialLinearGroup.coe_transpose, Matrix.SpecialLinearGroup.coe_inv, hXc,
        Matrix.adjugate_transpose, hsym]
    exact Matrix.SpecialLinearGroup.ext _ _ (fun i j => congrFun (congrFun h i) j)

open CFSG.ComponentClassification.CatalogueBHigherLinearAction in
theorem slConjugation_eq {A : GL (Fin 5) K} {A' : SpecialLinearGroup (Fin 5) K}
    (h : Matrix.SpecialLinearGroup.toGL A' = A) (g : SpecialLinearGroup (Fin 5) K) :
    slConjugation 5 K A g = A' * g * A'⁻¹ := by
  apply Matrix.SpecialLinearGroup.toGL_injective
  rw [toGL_slConjugation, map_mul, map_mul, map_inv, h]

theorem exists_sl_of_gl (hK : Nat.card K = 2) (A : GL (Fin 5) K) :
    ∃ A' : SpecialLinearGroup (Fin 5) K, Matrix.SpecialLinearGroup.toGL A' = A :=
  ⟨⟨A.1, det_eq_one hK A⟩, Units.ext rfl⟩

theorem automorphism_form (hK : Nat.card K = 2) (α : MulAut (projectiveSL 5 K)) :
    ∃ (A' : SpecialLinearGroup (Fin 5) K) (ε : ℕ), ε ≤ 1 ∧
      α = conjAut 5 K (Matrix.SpecialLinearGroup.toGL A') * dualAut 5 K ^ ε := by
  obtain ⟨A, σ, ε, hε, hα⟩ := (automorphism_generation (K := K) (n := 5) (by norm_num)).2 α
  obtain ⟨A', hA'⟩ := exists_sl_of_gl hK A
  refine ⟨A', ε, hε, ?_⟩
  have hσ : fieldAut 5 K σ = 1 := by
    ext p
    obtain ⟨g, rfl⟩ := proj_surjective 5 K p
    rw [fieldAut_proj]
    have : Matrix.SpecialLinearGroup.map σ.toRingHom g = g :=
      Matrix.SpecialLinearGroup.ext _ _ (fun i j => ringEquiv_apply hK σ (g i j))
    rw [this]
    rfl
  rw [hα, hσ, mul_one, hA']

end CFSG.EvenSporadicStandard.M22Std.P21L52
