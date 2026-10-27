module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareBasic

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquare

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

open CatalogueBProjectiveInvolution

theorem positive_eigenspace_sum (Q : QuadraticForm K V)
    (T : Module.End K V) (b : K) (hb : b ≠ 0) (h2 : (2 : K) ≠ 0)
    (hadj : ∀ x y : V, Q.polarBilin (T x) y = Q.polarBilin x (T y))
    (x : T.eigenspace b) (y : T.eigenspace (-b)) :
    Q (x.val + y.val) = Q x.val + Q y.val := by
  have ho := opposite_eigenspaces_orthogonal Q.polarBilin T b hb h2 hadj
    x.val y.val x.property y.property
  rw [QuadraticMap.map_add Q x.val y.val]
  change Q x.val + Q y.val + Q.polarBilin x.val y.val = _
  rw [ho, add_zero]

@[expose] def positiveOrthogonalExtension (Q : QuadraticForm K V)
    (T : Module.End K V) (b : K) (hb : b ≠ 0) (h2 : (2 : K) ≠ 0)
    (hsquare : T * T = b ^ 2 • (1 : Module.End K V))
    (hadj : ∀ x y : V, Q.polarBilin (T x) y = Q.polarBilin x (T y))
    (g : TauCeti.QuadraticMap.orthogonalGroup (Q.comp (T.eigenspace b).subtype) ×
      TauCeti.QuadraticMap.orthogonalGroup (Q.comp (T.eigenspace (-b)).subtype)) :
    orthogonalOperatorCentralizer Q T := by
  let f := splitCentralizerExtension T b hb h2 hsquare (g.1.val, g.2.val)
  refine ⟨⟨f.val, ?_⟩, f.property⟩
  apply TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr
  intro x
  obtain ⟨z, rfl⟩ := (squareScalar_eigenspaceEquiv T b hb h2 hsquare).surjective x
  change Q ((splitCentralizerExtension T b hb h2 hsquare (g.1.val, g.2.val)).val
    (squareScalar_eigenspaceEquiv T b hb h2 hsquare z)) = _
  rw [splitCentralizerExtension_apply]
  change Q ((g.1.val z.1).val + (g.2.val z.2).val) = Q (z.1.val + z.2.val)
  rw [positive_eigenspace_sum Q T b hb h2 hadj,
    positive_eigenspace_sum Q T b hb h2 hadj]
  exact congrArg₂ (· + ·) (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp g.1.property z.1)
    (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp g.2.property z.2)

theorem positiveOrthogonalExtension_apply (Q : QuadraticForm K V)
    (T : Module.End K V) (b : K) (hb : b ≠ 0) (h2 : (2 : K) ≠ 0)
    (hsquare : T * T = b ^ 2 • (1 : Module.End K V))
    (hadj : ∀ x y : V, Q.polarBilin (T x) y = Q.polarBilin x (T y))
    (g : TauCeti.QuadraticMap.orthogonalGroup (Q.comp (T.eigenspace b).subtype) ×
      TauCeti.QuadraticMap.orthogonalGroup (Q.comp (T.eigenspace (-b)).subtype))
    (x : T.eigenspace b × T.eigenspace (-b)) :
    (positiveOrthogonalExtension Q T b hb h2 hsquare hadj g).val.val
        (squareScalar_eigenspaceEquiv T b hb h2 hsquare x) =
      (g.1.val x.1).val + (g.2.val x.2).val :=
  splitCentralizerExtension_apply T b hb h2 hsquare (g.1.val, g.2.val) x

theorem splitOrthogonalRestriction_positive_extension (Q : QuadraticForm K V)
    (T : Module.End K V) (b : K) (hb : b ≠ 0) (h2 : (2 : K) ≠ 0)
    (hsquare : T * T = b ^ 2 • (1 : Module.End K V))
    (hadj : ∀ x y : V, Q.polarBilin (T x) y = Q.polarBilin x (T y))
    (g : TauCeti.QuadraticMap.orthogonalGroup (Q.comp (T.eigenspace b).subtype) ×
      TauCeti.QuadraticMap.orthogonalGroup (Q.comp (T.eigenspace (-b)).subtype)) :
    splitOrthogonalRestriction Q T b
      (positiveOrthogonalExtension Q T b hb h2 hsquare hadj g) = g := by
  apply Prod.ext
  · apply Subtype.ext
    ext x
    change (positiveOrthogonalExtension Q T b hb h2 hsquare hadj g).val.val x.val =
      (g.1.val x).val
    simpa [squareScalar_eigenspaceEquiv] using
      positiveOrthogonalExtension_apply Q T b hb h2 hsquare hadj g (x, 0)
  · apply Subtype.ext
    ext x
    change (positiveOrthogonalExtension Q T b hb h2 hsquare hadj g).val.val x.val =
      (g.2.val x).val
    simpa [squareScalar_eigenspaceEquiv] using
      positiveOrthogonalExtension_apply Q T b hb h2 hsquare hadj g (0, x)

theorem positive_extension_splitOrthogonalRestriction (Q : QuadraticForm K V)
    (T : Module.End K V) (b : K) (hb : b ≠ 0) (h2 : (2 : K) ≠ 0)
    (hsquare : T * T = b ^ 2 • (1 : Module.End K V))
    (hadj : ∀ x y : V, Q.polarBilin (T x) y = Q.polarBilin x (T y))
    (g : orthogonalOperatorCentralizer Q T) :
    positiveOrthogonalExtension Q T b hb h2 hsquare hadj
      (splitOrthogonalRestriction Q T b g) = g := by
  apply Subtype.ext
  apply Subtype.ext
  ext x
  obtain ⟨z, rfl⟩ := (squareScalar_eigenspaceEquiv T b hb h2 hsquare).surjective x
  rw [positiveOrthogonalExtension_apply]
  change g.val.val z.1.val + g.val.val z.2.val = g.val.val (z.1.val + z.2.val)
  exact (map_add g.val.val _ _).symm

@[expose] def positiveOrthogonalCentralizerEquiv (Q : QuadraticForm K V)
    (T : Module.End K V) (b : K) (hb : b ≠ 0) (h2 : (2 : K) ≠ 0)
    (hsquare : T * T = b ^ 2 • (1 : Module.End K V))
    (hadj : ∀ x y : V, Q.polarBilin (T x) y = Q.polarBilin x (T y)) :
    orthogonalOperatorCentralizer Q T ≃*
      (TauCeti.QuadraticMap.orthogonalGroup (Q.comp (T.eigenspace b).subtype) ×
        TauCeti.QuadraticMap.orthogonalGroup (Q.comp (T.eigenspace (-b)).subtype)) where
  toFun := splitOrthogonalRestriction Q T b
  invFun := positiveOrthogonalExtension Q T b hb h2 hsquare hadj
  left_inv := positive_extension_splitOrthogonalRestriction Q T b hb h2 hsquare hadj
  right_inv := splitOrthogonalRestriction_positive_extension Q T b hb h2 hsquare hadj
  map_mul' := (splitOrthogonalRestriction Q T b).map_mul

end CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquare
