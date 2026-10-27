module

public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalMcLBasic
public import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Polynomial.Basic
public import Std.Tactic.BVDecide.Normalize.Prop

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.ComponentClassification.OutcomeLocal

open Module

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem toMatrix_tv_basis {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι (ZMod 2) V)
    {i j : ι} (hij : i ≠ j) (c : ZMod 2) (h : (c • b.coord j) (b i) = 0) :
    LinearMap.toMatrix b b (tv (c • b.coord j) (b i) h : V →ₗ[ZMod 2] V) =
      Matrix.transvection i j c := by
  ext k l
  rw [LinearMap.toMatrix_apply, tv_apply, map_add, map_smul, LinearMap.smul_apply,
    Basis.coord_apply, Basis.repr_self, Basis.repr_self, Finsupp.add_apply, Finsupp.smul_apply,
    Matrix.transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply,
    Finsupp.single_apply, Finsupp.single_apply, Finsupp.single_apply]
  by_cases hlk : l = k <;> by_cases hlj : l = j <;> by_cases hik : i = k <;>
    simp_all [eq_comm]

theorem coord_smul_basis_eq_zero {ι : Type*} (b : Basis ι (ZMod 2) V) {i j : ι} (hij : i ≠ j)
    (c : ZMod 2) : (c • b.coord j) (b i) = 0 := by
  rw [LinearMap.smul_apply, Basis.coord_apply, Basis.repr_self, Finsupp.single_eq_of_ne' hij,
    smul_zero]

variable [FiniteDimensional (ZMod 2) V]

theorem eq_top_of_forall_inG {G : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) V)}
    (hG : ∀ (φ : Dual (ZMod 2) V) (a : V), φ a = 0 → InG G φ a) : G = ⊤ := by
  classical
  let b := Module.finBasis (ZMod 2) V
  have key : ∀ M : Matrix (Fin (finrank (ZMod 2) V)) (Fin (finrank (ZMod 2) V)) (ZMod 2),
      M.det ≠ 0 → ∃ u ∈ G, LinearMap.toMatrix b b (u : V →ₗ[ZMod 2] V) = M := by
    intro M hM
    refine Matrix.diagonal_transvection_induction_of_det_ne_zero
      (fun M => ∃ u ∈ G, LinearMap.toMatrix b b (u : V →ₗ[ZMod 2] V) = M) M hM ?_ ?_ ?_
    · intro D hD
      have hD1 : D = fun _ => 1 := by
        funext i
        have hne : D i ≠ 0 := by
          rw [Matrix.det_diagonal, Finset.prod_ne_zero_iff] at hD
          exact hD i (Finset.mem_univ i)
        exact (zmod2_eq_zero_or_one (D i)).resolve_left hne
      refine ⟨1, G.one_mem, ?_⟩
      rw [hD1, Matrix.diagonal_one]
      exact LinearMap.toMatrix_id b
    · intro t
      obtain ⟨h, hmem⟩ := hG _ _ (coord_smul_basis_eq_zero b t.hij t.c)
      exact ⟨_, hmem, toMatrix_tv_basis b t.hij t.c h⟩
    · rintro A B - - ⟨u, hu, rfl⟩ ⟨w, hw, rfl⟩
      exact ⟨u * w, G.mul_mem hu hw, by rw [Units.val_mul, LinearMap.toMatrix_mul]⟩
  rw [eq_top_iff]
  intro g _
  obtain ⟨u, hu, hug⟩ := key (LinearMap.toMatrix b b g) (by
    rw [LinearMap.det_toMatrix]
    exact (g.isUnit.map LinearMap.det).ne_zero)
  have hug' : u = g := Units.ext ((LinearMap.toMatrix b b).injective hug)
  exact hug' ▸ hu

end CFSG.ComponentClassification.OutcomeLocal
