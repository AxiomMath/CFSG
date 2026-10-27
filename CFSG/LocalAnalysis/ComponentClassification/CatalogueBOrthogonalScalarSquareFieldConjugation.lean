module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareFieldCoordinates

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquareField

open Polynomial

universe u v

variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]

@[expose] def conjugationHom [Nontrivial V] (T : Module.End K V) (d : K)
    (hns : ¬ IsSquare d) (hsquare : T ^ 2 = algebraMap K (Module.End K V) d) :
    scalarAlgebra T →ₐ[K] scalarAlgebra T := by
  letI := scalarField T d hns hsquare
  exact (AdjoinRoot.liftAlgHom (CatalogueBProjectiveQuadratic.quadraticPolynomial d)
    (Algebra.ofId K (scalarAlgebra T)) (-generator T) (by
      change aeval (-generator T) (CatalogueBProjectiveQuadratic.quadraticPolynomial d) = 0
      simp only [CatalogueBProjectiveQuadratic.quadraticPolynomial, map_sub, map_pow,
        aeval_X, aeval_C, neg_sq, generator_square T d hsquare, sub_self])).comp
          (evaluationEquiv T d hns hsquare).symm.toAlgHom

theorem conjugationHom_generator [Nontrivial V] (T : Module.End K V) (d : K)
    (hns : ¬ IsSquare d) (hsquare : T ^ 2 = algebraMap K (Module.End K V) d) :
    conjugationHom T d hns hsquare (generator T) = -generator T := by
  let := scalarField T d hns hsquare
  have hr : (evaluationEquiv T d hns hsquare).symm (generator T) =
      AdjoinRoot.root (CatalogueBProjectiveQuadratic.quadraticPolynomial d) := by
    apply (evaluationEquiv T d hns hsquare).injective
    rw [AlgEquiv.apply_symm_apply, evaluationEquiv_root]
  rw [conjugationHom, AlgHom.comp_apply]
  change AdjoinRoot.liftAlgHom _ _ _ _ ((evaluationEquiv T d hns hsquare).symm (generator T)) = _
  rw [hr]
  exact AdjoinRoot.liftAlgHom_root _ _ _ _

theorem conjugationHom_coordinates [Nontrivial V] (T : Module.End K V) (d : K)
    (hns : ¬ IsSquare d) (hsquare : T ^ 2 = algebraMap K (Module.End K V) d)
    (a b : K) :
    conjugationHom T d hns hsquare (coordinateElement T a b) = coordinateElement T a (-b) := by
  simp only [coordinateElement, map_add, AlgHom.commutes, map_smul,
    conjugationHom_generator, smul_neg, neg_smul]

theorem conjugationHom_involutive [Nontrivial V] (T : Module.End K V) (d : K)
    (hns : ¬ IsSquare d) (hsquare : T ^ 2 = algebraMap K (Module.End K V) d) :
    Function.Involutive (conjugationHom T d hns hsquare) := by
  intro z
  obtain ⟨p, hp, _⟩ := existsUnique_coordinates T d hns hsquare z
  rw [← hp, conjugationHom_coordinates, conjugationHom_coordinates, neg_neg]

@[expose] def conjugation [Nontrivial V] (T : Module.End K V) (d : K)
    (hns : ¬ IsSquare d) (hsquare : T ^ 2 = algebraMap K (Module.End K V) d) :
    scalarAlgebra T ≃ₐ[K] scalarAlgebra T :=
  AlgEquiv.ofAlgHom (conjugationHom T d hns hsquare) (conjugationHom T d hns hsquare)
    (AlgHom.ext (conjugationHom_involutive T d hns hsquare))
    (AlgHom.ext (conjugationHom_involutive T d hns hsquare))

theorem conjugation_apply [Nontrivial V] (T : Module.End K V) (d : K)
    (hns : ¬ IsSquare d) (hsquare : T ^ 2 = algebraMap K (Module.End K V) d)
    (z : scalarAlgebra T) :
    conjugation T d hns hsquare z = conjugationHom T d hns hsquare z := rfl

theorem conjugation_generator [Nontrivial V] (T : Module.End K V) (d : K)
    (hns : ¬ IsSquare d) (hsquare : T ^ 2 = algebraMap K (Module.End K V) d) :
    conjugation T d hns hsquare (generator T) = -generator T :=
  conjugationHom_generator T d hns hsquare

theorem conjugation_coordinates [Nontrivial V] (T : Module.End K V) (d : K)
    (hns : ¬ IsSquare d) (hsquare : T ^ 2 = algebraMap K (Module.End K V) d)
    (a b : K) :
    conjugation T d hns hsquare (coordinateElement T a b) = coordinateElement T a (-b) :=
  conjugationHom_coordinates T d hns hsquare a b

theorem conjugation_involutive [Nontrivial V] (T : Module.End K V) (d : K)
    (hns : ¬ IsSquare d) (hsquare : T ^ 2 = algebraMap K (Module.End K V) d) :
    Function.Involutive (conjugation T d hns hsquare) :=
  conjugationHom_involutive T d hns hsquare

theorem conjugation_symm [Nontrivial V] (T : Module.End K V) (d : K)
    (hns : ¬ IsSquare d) (hsquare : T ^ 2 = algebraMap K (Module.End K V) d) :
    (conjugation T d hns hsquare).symm = conjugation T d hns hsquare := by
  ext z
  rfl

theorem conjugation_square [Nontrivial V] (T : Module.End K V) (d : K)
    (hns : ¬ IsSquare d) (hsquare : T ^ 2 = algebraMap K (Module.End K V) d) :
    conjugation T d hns hsquare * conjugation T d hns hsquare = 1 := by
  apply AlgEquiv.ext
  intro z
  exact conjugation_involutive T d hns hsquare z

theorem generator_ne_zero [Nontrivial V] (T : Module.End K V) (d : K)
    (hns : ¬ IsSquare d) (hsquare : T ^ 2 = algebraMap K (Module.End K V) d) :
    generator T ≠ 0 := by
  intro hz
  have h := (coordinateElement_eq_zero_iff T d hns hsquare 0 1).mp
    ((coordinateElement_generator T).trans hz)
  exact one_ne_zero h.2

theorem conjugation_ne_one [Nontrivial V] (T : Module.End K V) (d : K)
    (hns : ¬ IsSquare d) (hsquare : T ^ 2 = algebraMap K (Module.End K V) d)
    (h2 : (2 : K) ≠ 0) : conjugation T d hns hsquare ≠ 1 := by
  intro h
  have hg := congrArg (fun f : scalarAlgebra T ≃ₐ[K] scalarAlgebra T => f (generator T)) h
  rw [conjugation_generator] at hg
  change -generator T = generator T at hg
  have hc := (coordinateElement_eq_iff T d hns hsquare 0 (-1) 0 1).mp (by
    simpa only [coordinateElement, map_zero, zero_add, neg_one_smul, one_smul] using hg)
  apply h2
  linear_combination -hc.2

theorem conjugation_fixed_iff [Nontrivial V] (T : Module.End K V) (d : K)
    (hns : ¬ IsSquare d) (hsquare : T ^ 2 = algebraMap K (Module.End K V) d)
    (h2 : (2 : K) ≠ 0) (z : scalarAlgebra T) :
    conjugation T d hns hsquare z = z ↔ ∃ a : K, z = algebraMap K (scalarAlgebra T) a := by
  constructor
  · intro hz
    obtain ⟨p, hp, _⟩ := existsUnique_coordinates T d hns hsquare z
    have hc := (coordinateElement_eq_iff T d hns hsquare p.1 (-p.2) p.1 p.2).mp (by
      rw [← conjugation_coordinates T d hns hsquare p.1 p.2, hp]
      exact hz)
    have hb : p.2 = 0 := by
      have hmul : (2 : K) * p.2 = 0 := by linear_combination -hc.2
      exact (mul_eq_zero.mp hmul).resolve_left h2
    refine ⟨p.1, ?_⟩
    rw [← hp, hb]
    simp only [coordinateElement, zero_smul, add_zero]
  · rintro ⟨a, rfl⟩
    exact (conjugation T d hns hsquare).commutes a

theorem conjugation_val_coordinates [Nontrivial V] (T : Module.End K V) (d : K)
    (hns : ¬ IsSquare d) (hsquare : T ^ 2 = algebraMap K (Module.End K V) d)
    (a b : K) :
    (conjugation T d hns hsquare (coordinateElement T a b)).val =
      algebraMap K (Module.End K V) a - b • T := by
  rw [conjugation_coordinates, coordinateElement_val, neg_smul]
  simp only [sub_eq_add_neg]

end CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquareField
