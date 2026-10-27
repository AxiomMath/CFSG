module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareFormsQuadratic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentFixedSpace

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalDescent

open CatalogueBLinearTwoDescent

universe u v

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]

abbrev originalQuadratic (B : LinearMap.BilinForm K V) : QuadraticForm K V :=
  CatalogueBOrthogonalScalarSquareForms.quadraticOfPolar B

theorem originalQuadratic_apply (B : LinearMap.BilinForm K V) (x : V) :
    originalQuadratic B x = B x x / 2 :=
  CatalogueBOrthogonalScalarSquareForms.quadraticOfPolar_apply B x

theorem originalQuadratic_polarBilin (B : LinearMap.BilinForm K V) (hsym : B.IsSymm)
    (h2 : (2 : K) ≠ 0) : (originalQuadratic B).polarBilin = B :=
  CatalogueBOrthogonalScalarSquareForms.quadraticOfPolar_polarBilin B hsym h2

theorem originalQuadratic_isometry_iff (B : LinearMap.BilinForm K V) (hsym : B.IsSymm)
    (h2 : (2 : K) ≠ 0) (g : V ≃ₗ[K] V) :
    g ∈ TauCeti.QuadraticMap.orthogonalGroup (originalQuadratic B) ↔
      ∀ x y, B (g x) (g y) = B x y :=
  CatalogueBOrthogonalScalarSquareForms.quadraticOfPolar_isometry_iff B hsym h2 g

variable (sigma : K ≃+* K) (T : V ≃+ V)
variable (hsemi : ∀ a x, T (a • x) = sigma a • T x)
variable (B : LinearMap.BilinForm K V) (c : Kˣ)
variable (hform : ∀ x y, (c : K) * B (T x) (T y) = sigma ((c : K) * B x y))

include hform in
theorem fixed_form_value (x y : fixedSubspace sigma T hsemi) :
    (c : K) * B (x : V) (y : V) ∈ fixedSubfield K sigma := by
  apply (mem_fixedSubfield K sigma _).mpr
  rw [← hform, x.property, y.property]

@[expose] def descendedBilinear :
    LinearMap.BilinForm (fixedSubfield K sigma) (fixedSubspace sigma T hsemi) :=
  LinearMap.restrictScalarsRange₂
    (fixedSubspace sigma T hsemi).subtype (fixedSubspace sigma T hsemi).subtype
    (Algebra.linearMap (fixedSubfield K sigma) K)
    (algebraMap (fixedSubfield K sigma) K).injective ((c : K) • B) (by
      intro x y
      refine ⟨⟨(c : K) * B (x : V) (y : V), fixed_form_value sigma T hsemi B c hform x y⟩, rfl⟩)

theorem descendedBilinear_apply (x y : fixedSubspace sigma T hsemi) :
    (descendedBilinear sigma T hsemi B c hform x y : K) = (c : K) * B (x : V) (y : V) := by
  exact LinearMap.restrictScalarsRange₂_apply
    (fixedSubspace sigma T hsemi).subtype (fixedSubspace sigma T hsemi).subtype
    (Algebra.linearMap (fixedSubfield K sigma) K)
    (algebraMap (fixedSubfield K sigma) K).injective ((c : K) • B) _ x y

theorem descendedBilinear_isSymm (hsym : B.IsSymm) :
    (descendedBilinear sigma T hsemi B c hform).IsSymm := by
  constructor
  intro x y
  apply Subtype.ext
  rw [descendedBilinear_apply, descendedBilinear_apply, hsym.eq]

include hform in
theorem descendedBilinear_nondegenerate [Module.Finite K V]
    (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1) (h2 : (2 : K) ≠ 0)
    (hT : Function.Involutive T) (hsym : B.IsSymm) (hnd : B.Nondegenerate) :
    (descendedBilinear sigma T hsemi B c hform).Nondegenerate := by
  have hleft : (descendedBilinear sigma T hsemi B c hform).SeparatingLeft := by
    intro x hx
    apply Subtype.ext
    change (x : V) = 0
    apply hnd.1
    obtain ⟨e, he⟩ := CatalogueBLinearDescent.exists_fixed_finrank_basis
      sigma hsigma hne h2 T hT hsemi
    have hzero (i : Fin (Module.finrank K V)) : B (x : V) (e i) = 0 := by
      have h := congrArg (fun a : fixedSubfield K sigma => (a : K)) (hx ⟨e i, he i⟩)
      rw [descendedBilinear_apply] at h
      exact (mul_eq_zero.mp h).resolve_left (Units.ne_zero c)
    have hmap : B (x : V) = 0 := by
      apply e.ext
      intro i
      exact hzero i
    intro y
    rw [hmap]
    rfl
  refine ⟨hleft, ?_⟩
  intro y hy
  apply hleft
  intro x
  rw [(descendedBilinear_isSymm sigma T hsemi B c hform hsym).eq]
  exact hy x

@[expose] def descendedQuadratic :
    QuadraticForm (fixedSubfield K sigma) (fixedSubspace sigma T hsemi) :=
  originalQuadratic (descendedBilinear sigma T hsemi B c hform)

theorem descendedQuadratic_apply (x : fixedSubspace sigma T hsemi) :
    descendedQuadratic sigma T hsemi B c hform x =
      descendedBilinear sigma T hsemi B c hform x x / 2 :=
  originalQuadratic_apply _ x

theorem descendedQuadratic_original_apply (x : fixedSubspace sigma T hsemi) :
    (descendedQuadratic sigma T hsemi B c hform x : K) = (c : K) * originalQuadratic B (x : V) := by
  change algebraMap (fixedSubfield K sigma) K (descendedQuadratic sigma T hsemi B c hform x) = _
  rw [descendedQuadratic_apply, map_div₀, map_ofNat]
  change (descendedBilinear sigma T hsemi B c hform x x : K) / 2 = _
  rw [descendedBilinear_apply, originalQuadratic_apply]
  ring

theorem fixedField_two_ne_zero (h2 : (2 : K) ≠ 0) : (2 : fixedSubfield K sigma) ≠ 0 := by
  intro h
  apply h2
  have h' := congrArg (fun a : fixedSubfield K sigma => (a : K)) h
  exact h'

theorem descendedQuadratic_polarBilin (hsym : B.IsSymm) (h2 : (2 : K) ≠ 0) :
    (descendedQuadratic sigma T hsemi B c hform).polarBilin =
      descendedBilinear sigma T hsemi B c hform :=
  originalQuadratic_polarBilin _ (descendedBilinear_isSymm sigma T hsemi B c hform hsym)
    (fixedField_two_ne_zero sigma h2)

theorem descendedQuadratic_isometry_iff (hsym : B.IsSymm) (h2 : (2 : K) ≠ 0)
    (f : (fixedSubspace sigma T hsemi) ≃ₗ[fixedSubfield K sigma] (fixedSubspace sigma T hsemi)) :
    f ∈ TauCeti.QuadraticMap.orthogonalGroup (descendedQuadratic sigma T hsemi B c hform) ↔
      ∀ x y, descendedBilinear sigma T hsemi B c hform (f x) (f y) =
        descendedBilinear sigma T hsemi B c hform x y :=
  originalQuadratic_isometry_iff _ (descendedBilinear_isSymm sigma T hsemi B c hform hsym)
    (fixedField_two_ne_zero sigma h2) f

end CFSG.ComponentClassification.CatalogueBOrthogonalDescent
