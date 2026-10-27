module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveQuadraticAction
public import Mathlib.Tactic.ENatToNat

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquareField

open Polynomial

universe u v

variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]

abbrev scalarAlgebra (T : Module.End K V) := Algebra.adjoin K ({T} : Set (Module.End K V))

@[expose] def generator (T : Module.End K V) : scalarAlgebra T :=
  ⟨T, Algebra.self_mem_adjoin_singleton K T⟩

theorem generator_val (T : Module.End K V) : (generator T).val = T := rfl

theorem scalarAlgebra_algebraMap_val (T : Module.End K V) (a : K) :
    (algebraMap K (scalarAlgebra T) a).val = algebraMap K (Module.End K V) a := rfl

theorem generator_square (T : Module.End K V) (d : K)
    (hsquare : T ^ 2 = algebraMap K (Module.End K V) d) :
    generator T ^ 2 = algebraMap K (scalarAlgebra T) d :=
  Subtype.ext hsquare

@[expose] def evaluationEquiv [Nontrivial V] (T : Module.End K V) (d : K)
    (hns : ¬ IsSquare d) (hsquare : T ^ 2 = algebraMap K (Module.End K V) d) :
    CatalogueBProjectiveQuadratic.extension d ≃ₐ[K] scalarAlgebra T := by
  letI : Fact (¬ IsSquare d) := ⟨hns⟩
  exact CatalogueBProjectiveQuadratic.actionAdjoinEquiv T d hsquare

theorem evaluationEquiv_val [Nontrivial V] (T : Module.End K V) (d : K)
    (hns : ¬ IsSquare d) (hsquare : T ^ 2 = algebraMap K (Module.End K V) d)
    (z : CatalogueBProjectiveQuadratic.extension d) :
    (evaluationEquiv T d hns hsquare z).val =
      CatalogueBProjectiveQuadratic.actionHom T d hsquare z := rfl

theorem evaluationEquiv_root [Nontrivial V] (T : Module.End K V) (d : K)
    (hns : ¬ IsSquare d) (hsquare : T ^ 2 = algebraMap K (Module.End K V) d) :
    evaluationEquiv T d hns hsquare
      (AdjoinRoot.root (CatalogueBProjectiveQuadratic.quadraticPolynomial d)) = generator T := by
  apply Subtype.ext
  exact CatalogueBProjectiveQuadratic.actionHom_root T d hsquare

theorem scalarAlgebra_isField [Nontrivial V] (T : Module.End K V) (d : K)
    (hns : ¬ IsSquare d) (hsquare : T ^ 2 = algebraMap K (Module.End K V) d) :
    IsField (scalarAlgebra T) := by
  let : Fact (¬ IsSquare d) := ⟨hns⟩
  let e := evaluationEquiv T d hns hsquare
  refine ⟨⟨0, 1, zero_ne_one⟩, ?_, ?_⟩
  · intro x y
    apply e.symm.injective
    simp only [map_mul]
    exact mul_comm _ _
  · intro x hx
    refine ⟨e ((e.symm x)⁻¹), ?_⟩
    apply e.symm.injective
    rw [map_mul, e.symm_apply_apply, map_one]
    exact mul_inv_cancel₀ (by simpa using hx)

@[expose, instance_reducible] def scalarField [Nontrivial V] (T : Module.End K V) (d : K)
    (hns : ¬ IsSquare d) (hsquare : T ^ 2 = algebraMap K (Module.End K V) d) :
    Field (scalarAlgebra T) :=
  (scalarAlgebra_isField T d hns hsquare).toField

@[expose] def basisIndex (d : K) :
    Fin (AdjoinRoot.powerBasis' (CatalogueBProjectiveQuadratic.quadraticPolynomial_monic d)).dim ≃
      Fin 2 where
    toFun := fun i => ⟨i.val, by
      simpa only [AdjoinRoot.powerBasis'_dim,
        CatalogueBProjectiveQuadratic.quadraticPolynomial_natDegree] using i.isLt⟩
    invFun := fun i => ⟨i.val, by
      simpa only [AdjoinRoot.powerBasis'_dim,
        CatalogueBProjectiveQuadratic.quadraticPolynomial_natDegree] using i.isLt⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl

theorem basisIndex_symm_val (d : K) (i : Fin 2) :
    ((basisIndex d).symm i).val = i.val := rfl

@[expose] def scalarBasis [Nontrivial V] (T : Module.End K V) (d : K)
    (hns : ¬ IsSquare d) (hsquare : T ^ 2 = algebraMap K (Module.End K V) d) :
    Module.Basis (Fin 2) K (scalarAlgebra T) :=
  ((AdjoinRoot.powerBasis' (CatalogueBProjectiveQuadratic.quadraticPolynomial_monic d)).basis.reindex
    (basisIndex d)).map (evaluationEquiv T d hns hsquare).toLinearEquiv

theorem scalarBasis_zero [Nontrivial V] (T : Module.End K V) (d : K)
    (hns : ¬ IsSquare d) (hsquare : T ^ 2 = algebraMap K (Module.End K V) d) :
    scalarBasis T d hns hsquare 0 = 1 := by
  rw [scalarBasis, Module.Basis.map_apply, Module.Basis.reindex_apply,
    PowerBasis.basis_eq_pow, basisIndex_symm_val]
  simp only [Fin.val_zero, pow_zero, AlgEquiv.toLinearEquiv_apply, map_one]

theorem scalarBasis_one [Nontrivial V] (T : Module.End K V) (d : K)
    (hns : ¬ IsSquare d) (hsquare : T ^ 2 = algebraMap K (Module.End K V) d) :
    scalarBasis T d hns hsquare 1 = generator T := by
  rw [scalarBasis, Module.Basis.map_apply, Module.Basis.reindex_apply,
    PowerBasis.basis_eq_pow, basisIndex_symm_val]
  simp only [Fin.val_one, pow_one, AdjoinRoot.powerBasis'_gen, AlgEquiv.toLinearEquiv_apply]
  exact evaluationEquiv_root T d hns hsquare

theorem scalarAlgebra_finite [Nontrivial V] (T : Module.End K V) (d : K)
    (hns : ¬ IsSquare d) (hsquare : T ^ 2 = algebraMap K (Module.End K V) d) :
    Module.Finite K (scalarAlgebra T) :=
  Module.Finite.of_basis (scalarBasis T d hns hsquare)

theorem scalarAlgebra_finrank [Nontrivial V] (T : Module.End K V) (d : K)
    (hns : ¬ IsSquare d) (hsquare : T ^ 2 = algebraMap K (Module.End K V) d) :
    Module.finrank K (scalarAlgebra T) = 2 := by
  rw [Module.finrank_eq_card_basis (scalarBasis T d hns hsquare), Fintype.card_fin]

theorem scalarAlgebra_card [Nontrivial V] (T : Module.End K V) (d : K)
    (hns : ¬ IsSquare d) (hsquare : T ^ 2 = algebraMap K (Module.End K V) d) :
    Nat.card (scalarAlgebra T) = Nat.card K ^ 2 := by
  let := scalarAlgebra_finite T d hns hsquare
  rw [Module.natCard_eq_pow_finrank (K := K), scalarAlgebra_finrank T d hns hsquare]

end CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquareField
