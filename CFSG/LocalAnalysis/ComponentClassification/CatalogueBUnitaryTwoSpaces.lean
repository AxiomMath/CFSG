module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBUnitaryTwoField

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBUnitaryTwo

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
open CatalogueBUnitaryIsometry

universe u v

variable {E : Type u} [Field E] (sigma : E ≃+* E)

@[expose] def specialIsometryMatrix
    (h : (Fin 2 → E) →ₛₗ[sigma.toRingHom] (Fin 2 → E) →ₗ[E] E)
    (g : specialIsometry h) : SpecialLinearGroup (Fin 2) E :=
  ⟨LinearMap.toMatrix' g.val.val.toLinearMap, by
    rw [LinearMap.det_toMatrix']
    exact (mem_specialIsometry_iff h g.val).mp g.property⟩

@[expose] def hyperbolicSpaceSLEquiv :
    specialIsometry (hyperbolicForm sigma) ≃* hyperbolicSpecialLinear sigma where
  toFun g := ⟨specialIsometryMatrix sigma (hyperbolicForm sigma) g, by
    rw [mem_hyperbolicSpecialLinear_iff]
    intro x y
    change hyperbolicForm sigma
      ((LinearMap.toMatrix' g.val.val.toLinearMap) *ᵥ x)
      ((LinearMap.toMatrix' g.val.val.toLinearMap) *ᵥ y) = _
    rw [LinearMap.toMatrix'_mulVec, LinearMap.toMatrix'_mulVec]
    exact g.val.property x y⟩
  invFun M := ⟨⟨SpecialLinearGroup.toLin' M.val, M.property⟩, by
    rw [mem_specialIsometry_iff]
    change LinearMap.det (Matrix.toLin' M.val.val) = 1
    rw [← LinearMap.det_toMatrix', LinearMap.toMatrix'_toLin']
    exact M.val.property⟩
  left_inv g := by
    apply Subtype.ext
    apply Subtype.ext
    apply LinearEquiv.toLinearMap_injective
    exact Matrix.toLin'_toMatrix' g.val.val.toLinearMap
  right_inv M := by
    apply Subtype.ext
    apply Subtype.ext
    exact LinearMap.toMatrix'_toLin' M.val.val
  map_mul' g j := by
    apply Subtype.ext
    apply Subtype.ext
    exact LinearMap.toMatrix'_mul g.val.val.toLinearMap j.val.val.toLinearMap

theorem hyperbolicSpaceSLEquiv_val (g : specialIsometry (hyperbolicForm sigma)) :
    (hyperbolicSpaceSLEquiv sigma g).val.val = LinearMap.toMatrix' g.val.val.toLinearMap :=
  rfl

variable {V : Type v} [AddCommGroup V] [Module E V]
  (h : V →ₛₗ[sigma.toRingHom] V →ₗ[E] E)

theorem hyperbolic_isometry_symm (B : (Fin 2 → E) ≃ₗ[E] V)
    (hB : ∀ x y, h (B x) (B y) = hyperbolicForm sigma x y) (x y : V) :
    hyperbolicForm sigma (B.symm x) (B.symm y) = h x y := by
  simpa only [B.apply_symm_apply] using (hB (B.symm x) (B.symm y)).symm

@[expose] def hyperbolicCoordinateEquiv (B : (Fin 2 → E) ≃ₗ[E] V)
    (hB : ∀ x y, h (B x) (B y) = hyperbolicForm sigma x y) :
    specialIsometry h ≃* hyperbolicSpecialLinear sigma :=
  (formSpecialIsometryEquiv h (hyperbolicForm sigma) B.symm
    (hyperbolic_isometry_symm sigma h B hB)).trans (hyperbolicSpaceSLEquiv sigma)

theorem hyperbolicCoordinateEquiv_val (B : (Fin 2 → E) ≃ₗ[E] V)
    (hB : ∀ x y, h (B x) (B y) = hyperbolicForm sigma x y) (g : specialIsometry h) :
    (hyperbolicCoordinateEquiv sigma h B hB g).val.val =
      LinearMap.toMatrix' ((B.trans g.val.val).trans B.symm).toLinearMap := rfl

@[expose] def specialIsometrySLEquiv (B : (Fin 2 → E) ≃ₗ[E] V)
    (hB : ∀ x y, h (B x) (B y) = hyperbolicForm sigma x y)
    (t : Eˣ) (ht : sigma (t : E) = -(t : E)) :
    specialIsometry h ≃*
      SpecialLinearGroup (Fin 2) (CatalogueBLinearTwoDescent.fixedSubfield E sigma) :=
  (hyperbolicCoordinateEquiv sigma h B hB).trans (hyperbolicSLEquiv sigma t ht)

theorem specialIsometrySLEquiv_forward (B : (Fin 2 → E) ≃ₗ[E] V)
    (hB : ∀ x y, h (B x) (B y) = hyperbolicForm sigma x y)
    (t : Eˣ) (ht : sigma (t : E) = -(t : E)) (g : specialIsometry h) :
    (fixedSLMap sigma (specialIsometrySLEquiv sigma h B hB t ht g)).val =
      (diagonalGL t)⁻¹.val *
        LinearMap.toMatrix' ((B.trans g.val.val).trans B.symm).toLinearMap *
        (diagonalGL t).val :=
  hyperbolicSLEquiv_forward sigma t ht (hyperbolicCoordinateEquiv sigma h B hB g)

theorem specialIsometrySLEquiv_inverse (B : (Fin 2 → E) ≃ₗ[E] V)
    (hB : ∀ x y, h (B x) (B y) = hyperbolicForm sigma x y)
    (t : Eˣ) (ht : sigma (t : E) = -(t : E))
    (N : SpecialLinearGroup (Fin 2) (CatalogueBLinearTwoDescent.fixedSubfield E sigma)) :
    LinearMap.toMatrix'
      ((B.trans ((specialIsometrySLEquiv sigma h B hB t ht).symm N).val.val).trans
        B.symm).toLinearMap =
      (diagonalGL t).val * (fixedSLMap sigma N).val * (diagonalGL t)⁻¹.val := by
  rw [← hyperbolicCoordinateEquiv_val sigma h B hB]
  have heq : hyperbolicCoordinateEquiv sigma h B hB
      ((specialIsometrySLEquiv sigma h B hB t ht).symm N) =
      (hyperbolicSLEquiv sigma t ht).symm N := by
    change hyperbolicCoordinateEquiv sigma h B hB
      ((hyperbolicCoordinateEquiv sigma h B hB).symm
        ((hyperbolicSLEquiv sigma t ht).symm N)) = _
    exact (hyperbolicCoordinateEquiv sigma h B hB).apply_symm_apply _
  rw [heq]
  exact hyperbolicSLEquiv_inverse sigma t ht N

theorem specialIsometrySLEquiv_inverse_apply (B : (Fin 2 → E) ≃ₗ[E] V)
    (hB : ∀ x y, h (B x) (B y) = hyperbolicForm sigma x y)
    (t : Eˣ) (ht : sigma (t : E) = -(t : E))
    (N : SpecialLinearGroup (Fin 2) (CatalogueBLinearTwoDescent.fixedSubfield E sigma))
    (v : V) :
    ((specialIsometrySLEquiv sigma h B hB t ht).symm N).val.val v =
      B (((diagonalGL t).val * (fixedSLMap sigma N).val * (diagonalGL t)⁻¹.val) *ᵥ
        B.symm v) := by
  rw [← specialIsometrySLEquiv_inverse sigma h B hB t ht N,
    LinearMap.toMatrix'_mulVec]
  simp

theorem exists_unitary_two_special_linear_isomorphism [Finite E] [FiniteDimensional E V]
    (hsym : h.IsSymm) (hnd : h.Nondegenerate)
    (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1) (hdim : Module.finrank E V = 2) :
    ∃ (B : (Fin 2 → E) ≃ₗ[E] V) (t : Eˣ)
      (e : specialIsometry h ≃*
        SpecialLinearGroup (Fin 2) (CatalogueBLinearTwoDescent.fixedSubfield E sigma)),
      (∀ x y, h (B x) (B y) = hyperbolicForm sigma x y) ∧
      (∀ i j, h (B (Pi.single i 1)) (B (Pi.single j 1)) = hyperbolicMatrix i j) ∧
      sigma (t : E) = -(t : E) ∧
      (∀ g : specialIsometry h,
        (fixedSLMap sigma (e g)).val = (diagonalGL t)⁻¹.val *
          LinearMap.toMatrix' ((B.trans g.val.val).trans B.symm).toLinearMap *
          (diagonalGL t).val) ∧
      (∀ N : SpecialLinearGroup (Fin 2) (CatalogueBLinearTwoDescent.fixedSubfield E sigma),
        LinearMap.toMatrix' ((B.trans (e.symm N).val.val).trans B.symm).toLinearMap =
          (diagonalGL t).val * (fixedSLMap sigma N).val * (diagonalGL t)⁻¹.val) := by
  obtain ⟨B, hB⟩ := exists_hyperbolic_isometry sigma h hsym hnd hsigma hne hdim
  obtain ⟨t, ht⟩ := exists_antifixed_unit sigma hsigma hne
  exact ⟨B, t, specialIsometrySLEquiv sigma h B hB t ht, hB,
    hyperbolic_isometry_gram sigma h B hB, ht,
    specialIsometrySLEquiv_forward sigma h B hB t ht,
    specialIsometrySLEquiv_inverse sigma h B hB t ht⟩

end CFSG.ComponentClassification.CatalogueBUnitaryTwo
