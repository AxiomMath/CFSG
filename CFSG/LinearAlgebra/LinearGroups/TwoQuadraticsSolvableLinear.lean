module

public import CFSG.LinearAlgebra.LinearGroups.TwoQuadraticsSolvable
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

public section

namespace CFSG.LinearGroups

open Matrix

universe u v

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

@[expose] noncomputable def closureEmbedding (L : Type u) [Field L] [Algebra K L]
    (b : Module.Basis (Fin (Module.finrank K V)) K V) :
    LinearMap.GeneralLinearGroup K V →*
      LinearMap.GeneralLinearGroup L (Fin (Module.finrank K V) → L) :=
  (Units.map (Matrix.toLinAlgEquiv' : Matrix (Fin (Module.finrank K V)) (Fin (Module.finrank K V)) L
      ≃ₐ[L] Module.End L (Fin (Module.finrank K V) → L)).toMonoidHom).comp
    ((Units.map (algebraMap K L).mapMatrix.toMonoidHom).comp
      (Units.map (LinearMap.toMatrixAlgEquiv b).toMonoidHom))

omit [FiniteDimensional K V] in
theorem closureEmbedding_coe (L : Type u) [Field L] [Algebra K L]
    (b : Module.Basis (Fin (Module.finrank K V)) K V) (g : LinearMap.GeneralLinearGroup K V) :
    ((closureEmbedding L b g : LinearMap.GeneralLinearGroup L _) :
        Module.End L (Fin (Module.finrank K V) → L)) =
      Matrix.toLinAlgEquiv' ((LinearMap.toMatrixAlgEquiv b (g : Module.End K V)).map
        (algebraMap K L)) := rfl

omit [FiniteDimensional K V] in
theorem closureEmbedding_injective (L : Type u) [Field L] [Algebra K L]
    (b : Module.Basis (Fin (Module.finrank K V)) K V) :
    Function.Injective (closureEmbedding L b) := by
  intro g h hgh
  apply Units.ext
  have h1 := congrArg (fun x : LinearMap.GeneralLinearGroup L _ =>
    (x : Module.End L (Fin (Module.finrank K V) → L))) hgh
  simp only [closureEmbedding_coe] at h1
  have h2 := Matrix.toLinAlgEquiv'.injective h1
  have h3 := Matrix.map_injective (algebraMap K L).injective h2
  exact (LinearMap.toMatrixAlgEquiv b).injective h3

omit [FiniteDimensional K V] in
theorem closureEmbedding_quadratic (L : Type u) [Field L] [Algebra K L]
    (b : Module.Basis (Fin (Module.finrank K V)) K V) {g : LinearMap.GeneralLinearGroup K V}
    (hg : ((g : V →ₗ[K] V) - 1) ^ 2 = 0) :
    ((closureEmbedding L b g : Module.End L (Fin (Module.finrank K V) → L)) - 1) ^ 2 = 0 := by
  rw [closureEmbedding_coe, ← map_one Matrix.toLinAlgEquiv', ← map_sub, ← map_pow]
  have h1 : (LinearMap.toMatrixAlgEquiv b (g : Module.End K V)).map (algebraMap K L) - 1 =
      (algebraMap K L).mapMatrix (LinearMap.toMatrixAlgEquiv b ((g : Module.End K V) - 1)) := by
    rw [map_sub, map_one, map_sub, map_one]
    rfl
  rw [h1, ← map_pow, ← map_pow, hg, map_zero, map_zero, map_zero]

theorem two_quadratics_solvable_linear {p : ℕ} (hp : p.Prime) (hodd : Odd p) [CharP K p]
    (a b : LinearMap.GeneralLinearGroup K V) (ha : ((a : V →ₗ[K] V) - 1) ^ 2 = 0)
    (hb : ((b : V →ₗ[K] V) - 1) ^ 2 = 0)
    [Finite (Subgroup.closure ({a, b} : Set (LinearMap.GeneralLinearGroup K V)))]
    (hsolv : Group.IsSolvable
      (Subgroup.closure ({a, b} : Set (LinearMap.GeneralLinearGroup K V))))
    (halt : 5 ≤ p ∨
      Odd (Nat.card (Subgroup.closure ({a, b} : Set (LinearMap.GeneralLinearGroup K V))))) :
    IsPGroup p (Subgroup.closure ({a, b} : Set (LinearMap.GeneralLinearGroup K V))) := by
  let L := AlgebraicClosure K
  have : CharP L p := charP_of_injective_algebraMap (algebraMap K L).injective p
  let b₀ := Module.finBasis K V
  let F := closureEmbedding L b₀
  have hF := closureEmbedding_injective L b₀
  let H := Subgroup.closure ({a, b} : Set (LinearMap.GeneralLinearGroup K V))
  have hmap : H.map F = Subgroup.closure ({F a, F b} : Set _) := by
    rw [MonoidHom.map_closure, Set.image_pair]
  let e : H ≃* H.map F := H.equivMapOfInjective F hF
  have : Finite (Subgroup.closure ({F a, F b} : Set _)) := by
    rw [← hmap]
    exact Finite.of_equiv _ e.toEquiv
  have hsolv' : Group.IsSolvable (Subgroup.closure ({F a, F b} : Set _)) := by
    rw [← hmap]
    exact Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
  have hcard : Nat.card (Subgroup.closure ({F a, F b} : Set _)) = Nat.card H := by
    rw [← hmap]
    exact (Nat.card_congr e.toEquiv).symm
  have halt' : 5 ≤ p ∨ Odd (Nat.card (Subgroup.closure ({F a, F b} : Set _))) := by
    rw [hcard]
    exact halt
  have hP := two_quadratics_solvable_algebraically_closed hp hodd (F a) (F b)
    (closureEmbedding_quadratic L b₀ ha) (closureEmbedding_quadratic L b₀ hb) hsolv' halt'
  rw [← hmap] at hP
  exact hP.of_equiv e.symm

end CFSG.LinearGroups
