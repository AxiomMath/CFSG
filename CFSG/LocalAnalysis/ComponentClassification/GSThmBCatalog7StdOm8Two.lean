module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7StdOm8Low
public import CFSG.GroupTheory.WeirSylow.OrthogonalModels

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB.Catalog7Std.Om8

open CFSG Subgroup Module
open CFSG.GroupTheory.WeirSylow (IsPlusType)
open CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquare
open CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquareField
open CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquareForms

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Nontrivial V]

omit [Finite K] [FiniteDimensional K V] in
theorem eq_zero_of_coordinate (T : Module.End K V) (d : K) (hns : ¬ IsSquare d)
    (hsquare : T ^ 2 = algebraMap K (Module.End K V) d) (a b : K)
    (h : algebraMap K (scalarAlgebra T) a + algebraMap K (scalarAlgebra T) b * generator T = 0) :
    a = 0 ∧ b = 0 := by
  have hind := (scalarBasis T d hns hsquare).linearIndependent
  have h' : a • scalarBasis T d hns hsquare 0 + b • scalarBasis T d hns hsquare 1 = 0 := by
    rw [scalarBasis_zero, scalarBasis_one, ← h, Algebra.smul_def, Algebra.smul_def, mul_one]
  have hind' : LinearIndependent K
      ![scalarBasis T d hns hsquare 0, scalarBasis T d hns hsquare 1] := by
    convert hind using 1
    funext i
    fin_cases i <;> rfl
  exact LinearIndependent.pair_iff.mp hind' a b h'

omit [Finite K] [FiniteDimensional K V] [Nontrivial V] in
theorem polarBilin_self (Q : QuadraticForm K V) (x : V) : Q.polarBilin x x = 2 * Q x := by
  rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self, two_nsmul, two_mul]

omit [FiniteDimensional K V] in
theorem actualPositive_not_split (hodd : Odd (Nat.card K)) (Q : QuadraticForm K V)
    (hdim : finrank K V = 8) (hnp : ¬ IsPlusType Q) (T : Module.End K V) (d : K) (hd : d ≠ 0)
    (hns : ¬ IsSquare d) (hsquare : T ^ 2 = algebraMap K (Module.End K V) d)
    (hadj : ∀ x y, Q.polarBilin (T x) y = Q.polarBilin x (T y)) :
    letI := scalarField T d hns hsquare
    letI := evaluationModule T
    ¬ ∃ S : Submodule (scalarAlgebra T) V, finrank (scalarAlgebra T) S = 2 ∧
      ∀ x ∈ S, actualPositiveQuadratic Q T d hd hns hsquare hadj x = 0 := by
  let := scalarField T d hns hsquare
  let := evaluationModule T
  let := evaluationScalarTower T
  let := scalarAlgebra_finite T d hns hsquare
  have h2 : (2 : K) ≠ 0 := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
  rintro ⟨S, hS2, hSQ⟩
  apply hnp
  refine ⟨S.restrictScalars K, ?_, fun x hx => ?_⟩
  · have : Module.Free (scalarAlgebra T) S := Module.Free.of_divisionRing _ _
    have : Module.Free K (scalarAlgebra T) := Module.Free.of_divisionRing _ _
    have h1 : finrank K (S.restrictScalars K) = finrank K (scalarAlgebra T) *
        finrank (scalarAlgebra T) S := (Module.finrank_mul_finrank K (scalarAlgebra T) S).symm
    rw [h1, hS2, scalarAlgebra_finrank T d hns hsquare, hdim]
  · have h0 := hSQ x hx
    rw [actualPositiveQuadratic_formula, div_eq_zero_iff] at h0
    rcases h0 with h0 | h0
    · obtain ⟨hxx, -⟩ := eq_zero_of_coordinate T d hns hsquare _ _ h0
      rw [polarBilin_self] at hxx
      exact (mul_eq_zero.mp hxx).resolve_left h2
    · exact absurd h0 (extension_two_ne_zero h2)

theorem actualPositive_pComponent {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hK : Nat.card K = p ^ f) (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
    (hdim : finrank K V = 8) (hnp : ¬ IsPlusType Q) (T : Module.End K V) (d : K) (hd : d ≠ 0)
    (hns : ¬ IsSquare d) (hsquare : T ^ 2 = algebraMap K (Module.End K V) d)
    (hadj : ∀ x y, Q.polarBilin (T x) y = Q.polarBilin x (T y)) :
    letI := scalarField T d hns hsquare
    letI := evaluationModule T
    ∀ M : Subgroup (TauCeti.QuadraticMap.orthogonalGroup
        (actualPositiveQuadratic Q T d hd hns hsquare hadj)),
      IsPComponent 2 M → IsQuasisimple M ∧
        Blueprint.LieModel (M ⧸ center M) .PSL 2 p (2 * (2 * f)) := by
  let := scalarField T d hns hsquare
  let := evaluationModule T
  let := evaluationScalarTower T
  let := scalarAlgebra_finite_type T d hns hsquare
  let := evaluationModule_finite T
  have hodd : Odd (Nat.card K) := by rw [hK]; exact (hp.eq_two_or_odd'.resolve_left hp2).pow
  have h2 : (2 : K) ≠ 0 := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
  intro M hM
  have hE : Nat.card (scalarAlgebra T) = p ^ (2 * f) := by
    rw [scalarAlgebra_card T d hns hsquare, hK, ← pow_mul, mul_comm]
  have hdimE : finrank (scalarAlgebra T) V = 4 := by
    rw [evaluationModule_finrank_div_two T d hns hsquare, hdim]
  have hQE := actualPositiveQuadratic_nondegenerate Q T d hd hns hsquare hadj hQ h2
  have hEodd : Odd (Nat.card (scalarAlgebra T)) := by
    rw [hE]
    exact (hp.eq_two_or_odd'.resolve_left hp2).pow
  exact ⟨(isComponent_of_pComponent hEodd hQE hM).1, (pComponent_nonsplit_four hp hp2 (by omega)
    hE hQE hdimE (actualPositive_not_split hodd Q hdim hnp T d hd hns hsquare hadj) hM).2⟩

end CFSG.ComponentClassification.GSThmB.Catalog7Std.Om8
