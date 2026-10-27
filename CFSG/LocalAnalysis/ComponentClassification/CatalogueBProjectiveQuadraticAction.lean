module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveQuadraticField

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBProjectiveQuadratic

open Polynomial

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem quadratic_aeval_eq_zero (T : Module.End K V) (lambda : K)
    (hsq : T ^ 2 = algebraMap K (Module.End K V) lambda) :
    aeval T (quadraticPolynomial lambda) = 0 := by
  simp only [quadraticPolynomial, map_sub, map_pow, aeval_X, aeval_C, hsq, sub_self]

@[expose] def actionHom (T : Module.End K V) (lambda : K)
    (hsq : T ^ 2 = algebraMap K (Module.End K V) lambda) :
    extension lambda →ₐ[K] Module.End K V :=
  Ideal.Quotient.liftₐ (Ideal.span {quadraticPolynomial lambda}) (aeval T) (by
    have hle : Ideal.span {quadraticPolynomial lambda} ≤ RingHom.ker (aeval T).toRingHom :=
      (Ideal.span_singleton_le_iff_mem _).mpr (quadratic_aeval_eq_zero T lambda hsq)
    intro p hp
    exact hle hp)

theorem actionHom_mk (T : Module.End K V) (lambda : K)
    (hsq : T ^ 2 = algebraMap K (Module.End K V) lambda) (p : K[X]) :
    actionHom T lambda hsq (AdjoinRoot.mk (quadraticPolynomial lambda) p) = aeval T p :=
  rfl

theorem actionHom_root (T : Module.End K V) (lambda : K)
    (hsq : T ^ 2 = algebraMap K (Module.End K V) lambda) :
    actionHom T lambda hsq (AdjoinRoot.root (quadraticPolynomial lambda)) = T :=
  aeval_X T

theorem actionHom_algebraMap (T : Module.End K V) (lambda : K)
    (hsq : T ^ 2 = algebraMap K (Module.End K V) lambda) (c : K) :
    actionHom T lambda hsq (algebraMap K (extension lambda) c) =
      algebraMap K (Module.End K V) c :=
  (actionHom T lambda hsq).commutes c

theorem actionHom_range (T : Module.End K V) (lambda : K)
    (hsq : T ^ 2 = algebraMap K (Module.End K V) lambda) :
    (actionHom T lambda hsq).range = Algebra.adjoin K {T} := by
  rw [Algebra.adjoin_singleton_eq_range_aeval]
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    induction x using AdjoinRoot.induction_on with
    | ih p => exact ⟨p, (actionHom_mk T lambda hsq p).symm⟩
  · rintro ⟨p, rfl⟩
    exact ⟨AdjoinRoot.mk (quadraticPolynomial lambda) p, actionHom_mk T lambda hsq p⟩

theorem actionHom_injective [Nontrivial V] (T : Module.End K V) (lambda : K)
    [Fact (¬ IsSquare lambda)]
    (hsq : T ^ 2 = algebraMap K (Module.End K V) lambda) :
    Function.Injective (actionHom T lambda hsq) :=
  (actionHom T lambda hsq).toRingHom.injective

@[expose] def actionAdjoinHom (T : Module.End K V) (lambda : K)
    (hsq : T ^ 2 = algebraMap K (Module.End K V) lambda) :
    extension lambda →ₐ[K] Algebra.adjoin K {T} :=
  (actionHom T lambda hsq).codRestrict (Algebra.adjoin K {T}) (fun x => by
    rw [← actionHom_range T lambda hsq]
    exact ⟨x, rfl⟩)

@[expose] def actionAdjoinEquiv [Nontrivial V] (T : Module.End K V) (lambda : K)
    [Fact (¬ IsSquare lambda)]
    (hsq : T ^ 2 = algebraMap K (Module.End K V) lambda) :
    extension lambda ≃ₐ[K] Algebra.adjoin K {T} :=
  AlgEquiv.ofBijective (actionAdjoinHom T lambda hsq) ⟨
    fun _ _ h => actionHom_injective T lambda hsq (congrArg Subtype.val h), by
    intro y
    have hy : y.val ∈ (actionHom T lambda hsq).range := by
      rw [actionHom_range]
      exact y.property
    obtain ⟨x, hx⟩ := hy
    exact ⟨x, Subtype.ext hx⟩⟩

theorem actionAdjoinEquiv_apply [Nontrivial V] (T : Module.End K V) (lambda : K)
    [Fact (¬ IsSquare lambda)]
    (hsq : T ^ 2 = algebraMap K (Module.End K V) lambda) (x : extension lambda) :
    (actionAdjoinEquiv T lambda hsq x : Module.End K V) = actionHom T lambda hsq x :=
  rfl

@[expose, instance_reducible] def actionModule (T : Module.End K V) (lambda : K)
    (hsq : T ^ 2 = algebraMap K (Module.End K V) lambda) : Module (extension lambda) V :=
  Module.compHom V (actionHom T lambda hsq).toRingHom

theorem actionModule_smul (T : Module.End K V) (lambda : K)
    (hsq : T ^ 2 = algebraMap K (Module.End K V) lambda)
    (x : extension lambda) (v : V) :
    letI := actionModule T lambda hsq
    x • v = actionHom T lambda hsq x v :=
  rfl

theorem actionModule_root_smul (T : Module.End K V) (lambda : K)
    (hsq : T ^ 2 = algebraMap K (Module.End K V) lambda) (v : V) :
    letI := actionModule T lambda hsq
    AdjoinRoot.root (quadraticPolynomial lambda) • v = T v := by
  change actionHom T lambda hsq _ v = T v
  rw [actionHom_root]

theorem actionModule_algebraMap_smul (T : Module.End K V) (lambda : K)
    (hsq : T ^ 2 = algebraMap K (Module.End K V) lambda) (c : K) (v : V) :
    letI := actionModule T lambda hsq
    algebraMap K (extension lambda) c • v = c • v := by
  change actionHom T lambda hsq _ v = c • v
  rw [actionHom_algebraMap]
  rfl

theorem actionScalarTower (T : Module.End K V) (lambda : K)
    (hsq : T ^ 2 = algebraMap K (Module.End K V) lambda) :
    letI := actionModule T lambda hsq
    IsScalarTower K (extension lambda) V := by
  let := actionModule T lambda hsq
  exact IsScalarTower.of_algebraMap_smul (actionModule_algebraMap_smul T lambda hsq)

end CFSG.ComponentClassification.CatalogueBProjectiveQuadratic
