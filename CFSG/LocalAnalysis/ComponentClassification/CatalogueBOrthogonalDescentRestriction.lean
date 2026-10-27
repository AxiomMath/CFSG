module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentForm

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalDescent

open CatalogueBLinearTwoDescent

universe u v

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]

@[expose] def linearPermutationAction : (V ≃ₗ[K] V) →* Equiv.Perm V where
  toFun := LinearEquiv.toEquiv
  map_one' := rfl
  map_mul' _ _ := rfl

@[expose] def semilinearOrthogonalCentralizer (Q : QuadraticForm K V) (T : V ≃+ V) :
    Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q) :=
  (Subgroup.centralizer {T.toEquiv}).comap
    (linearPermutationAction.comp (TauCeti.QuadraticMap.orthogonalGroup Q).subtype)

theorem mem_semilinearOrthogonalCentralizer_iff (Q : QuadraticForm K V) (T : V ≃+ V)
    (g : TauCeti.QuadraticMap.orthogonalGroup Q) :
    g ∈ semilinearOrthogonalCentralizer Q T ↔ ∀ x, g.val (T x) = T (g.val x) := by
  change (linearPermutationAction g.val) ∈ Subgroup.centralizer {T.toEquiv} ↔ _
  rw [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h x
    exact congrArg (fun e : Equiv.Perm V => e x) h
  · intro h
    ext x
    exact h x

theorem semilinearOrthogonalCentralizer_commutes (Q : QuadraticForm K V) (T : V ≃+ V)
    (g : semilinearOrthogonalCentralizer Q T) (x : V) :
    g.val.val (T x) = T (g.val.val x) :=
  (mem_semilinearOrthogonalCentralizer_iff Q T g.val).mp g.property x

variable (sigma : K ≃+* K) (T : V ≃+ V)
variable (hsemi : ∀ a x, T (a • x) = sigma a • T x)

theorem centralizer_preserves_fixed (Q : QuadraticForm K V)
    (g : semilinearOrthogonalCentralizer Q T) (x : fixedSubspace sigma T hsemi) :
    g.val.val (x : V) ∈ fixedSubspace sigma T hsemi := by
  change T (g.val.val (x : V)) = g.val.val (x : V)
  rw [← semilinearOrthogonalCentralizer_commutes, x.property]

@[expose] def centralizerFixedEquiv (Q : QuadraticForm K V)
    (g : semilinearOrthogonalCentralizer Q T) :
    (fixedSubspace sigma T hsemi) ≃ₗ[fixedSubfield K sigma] (fixedSubspace sigma T hsemi) where
  toFun x := ⟨g.val.val (x : V), centralizer_preserves_fixed sigma T hsemi Q g x⟩
  invFun x := ⟨g.val.val.symm (x : V), centralizer_preserves_fixed sigma T hsemi Q g⁻¹ x⟩
  left_inv x := Subtype.ext (g.val.val.symm_apply_apply (x : V))
  right_inv x := Subtype.ext (g.val.val.apply_symm_apply (x : V))
  map_add' x y := Subtype.ext (map_add g.val.val (x : V) (y : V))
  map_smul' a x := Subtype.ext (map_smul g.val.val (a : K) (x : V))

theorem centralizerFixedEquiv_apply (Q : QuadraticForm K V)
    (g : semilinearOrthogonalCentralizer Q T) (x : fixedSubspace sigma T hsemi) :
    (centralizerFixedEquiv sigma T hsemi Q g x : V) = g.val.val (x : V) := rfl

theorem centralizerFixedEquiv_symm_apply (Q : QuadraticForm K V)
    (g : semilinearOrthogonalCentralizer Q T) (x : fixedSubspace sigma T hsemi) :
    ((centralizerFixedEquiv sigma T hsemi Q g).symm x : V) = g.val.val.symm (x : V) := rfl

variable (B : LinearMap.BilinForm K V) (hsym : B.IsSymm) (h2 : (2 : K) ≠ 0)
variable (c : Kˣ)
variable (hform : ∀ x y, (c : K) * B (T x) (T y) = sigma ((c : K) * B x y))

@[expose] def orthogonalFixedRestriction :
    semilinearOrthogonalCentralizer (originalQuadratic B) T →*
      TauCeti.QuadraticMap.orthogonalGroup (descendedQuadratic sigma T hsemi B c hform) where
  toFun g := ⟨centralizerFixedEquiv sigma T hsemi (originalQuadratic B) g, by
    apply (descendedQuadratic_isometry_iff sigma T hsemi B c hform hsym h2 _).mpr
    intro x y
    apply Subtype.ext
    rw [descendedBilinear_apply, descendedBilinear_apply, centralizerFixedEquiv_apply,
      centralizerFixedEquiv_apply,
      (originalQuadratic_isometry_iff B hsym h2 g.val.val).mp g.val.property]⟩
  map_one' := by ext x; rfl
  map_mul' _ _ := by ext x; rfl

theorem orthogonalFixedRestriction_apply
    (g : semilinearOrthogonalCentralizer (originalQuadratic B) T)
    (x : fixedSubspace sigma T hsemi) :
    ((orthogonalFixedRestriction sigma T hsemi B hsym h2 c hform g).val x : V) =
      g.val.val (x : V) := rfl

theorem orthogonalFixedRestriction_symm_apply
    (g : semilinearOrthogonalCentralizer (originalQuadratic B) T)
    (x : fixedSubspace sigma T hsemi) :
    (((orthogonalFixedRestriction sigma T hsemi B hsym h2 c hform g).val).symm x : V) =
      g.val.val.symm (x : V) := rfl

end CFSG.ComponentClassification.CatalogueBOrthogonalDescent
