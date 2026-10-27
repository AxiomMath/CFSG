module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareFieldConjugation

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquareField

universe u v

variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]

theorem scalarAlgebra_finite_type [Finite K] [Nontrivial V] (T : Module.End K V) (d : K)
    (hns : ¬ IsSquare d) (hsquare : T ^ 2 = algebraMap K (Module.End K V) d) :
    Finite (scalarAlgebra T) := by
  let := scalarAlgebra_finite T d hns hsquare
  exact Module.finite_of_finite K

theorem conjugation_eq_card_power [Finite K] [Nontrivial V] (T : Module.End K V) (d : K)
    (hns : ¬ IsSquare d) (hsquare : T ^ 2 = algebraMap K (Module.End K V) d)
    (h2 : (2 : K) ≠ 0) (z : scalarAlgebra T) :
    letI := scalarField T d hns hsquare
    conjugation T d hns hsquare z = z ^ Nat.card K := by
  let := scalarField T d hns hsquare
  let := scalarAlgebra_finite_type T d hns hsquare
  let := Fintype.ofFinite K
  obtain ⟨i, hi⟩ := (FiniteField.bijective_frobeniusAlgHom_pow K (scalarAlgebra T)).surjective
    (conjugation T d hns hsquare).toAlgHom
  dsimp only at hi
  have hlt : i.val < 2 := by
    simpa only [scalarAlgebra_finrank T d hns hsquare] using i.isLt
  have hi0 : i.val ≠ 0 := by
    intro hz
    have hhom : (conjugation T d hns hsquare).toAlgHom = 1 := by
      rw [hz, pow_zero] at hi
      exact hi.symm
    apply conjugation_ne_one T d hns hsquare h2
    apply AlgEquiv.ext
    intro x
    exact congrArg (fun f : scalarAlgebra T →ₐ[K] scalarAlgebra T => f x) hhom
  have hi1 : i.val = 1 := by omega
  rw [hi1, pow_one] at hi
  have hx := congrArg (fun f : scalarAlgebra T →ₐ[K] scalarAlgebra T => f z) hi
  change z ^ Fintype.card K = conjugation T d hns hsquare z at hx
  rw [Fintype.card_eq_nat_card] at hx
  exact hx.symm

theorem finite_nonsquare_two_ne_zero [Finite K] (d : K) (hns : ¬ IsSquare d) :
    (2 : K) ≠ 0 := by
  apply Ring.two_ne_zero
  intro hchar
  exact hns (FiniteField.isSquare_of_char_two hchar d)

theorem finite_conjugation_eq_card_power [Finite K] [Nontrivial V]
    (T : Module.End K V) (d : K) (hns : ¬ IsSquare d)
    (hsquare : T ^ 2 = algebraMap K (Module.End K V) d) (z : scalarAlgebra T) :
    letI := scalarField T d hns hsquare
    conjugation T d hns hsquare z = z ^ Nat.card K :=
  conjugation_eq_card_power T d hns hsquare (finite_nonsquare_two_ne_zero d hns) z

theorem generator_card_power [Finite K] [Nontrivial V] (T : Module.End K V) (d : K)
    (hns : ¬ IsSquare d) (hsquare : T ^ 2 = algebraMap K (Module.End K V) d)
    (h2 : (2 : K) ≠ 0) :
    letI := scalarField T d hns hsquare
    generator T ^ Nat.card K = -generator T := by
  let := scalarField T d hns hsquare
  rw [← conjugation_eq_card_power T d hns hsquare h2, conjugation_generator]

theorem coordinate_card_power [Finite K] [Nontrivial V] (T : Module.End K V) (d : K)
    (hns : ¬ IsSquare d) (hsquare : T ^ 2 = algebraMap K (Module.End K V) d)
    (h2 : (2 : K) ≠ 0) (a b : K) :
    letI := scalarField T d hns hsquare
    coordinateElement T a b ^ Nat.card K = coordinateElement T a (-b) := by
  let := scalarField T d hns hsquare
  rw [← conjugation_eq_card_power T d hns hsquare h2, conjugation_coordinates]

end CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquareField
