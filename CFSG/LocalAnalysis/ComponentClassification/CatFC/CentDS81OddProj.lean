module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentDS81LieAPI
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentDS81Basic
public import CFSG.Assembly.GL83LieDefs
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentDS81LieCentral

public section

namespace CFSG.ComponentClassification.CatFC.DS81

open Subgroup CFSG CFSG.Open

theorem solvableOrComponent_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) (τ : X)
    (h : SolvableOrComponent Y (e τ)) : SolvableOrComponent X τ :=
  HasCompOrSolv.of_mulEquiv (centEquiv e τ).symm h

section Classical

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

@[expose] def MatrixDichotomy (H : Subgroup (Matrix.GeneralLinearGroup ι K)) : Prop :=
  ∀ h : H, (∃ u : Kˣ, (h : Matrix.GeneralLinearGroup ι K) ^ 2 =
      Matrix.GeneralLinearGroup.scalar ι u) →
    (h : Matrix.GeneralLinearGroup ι K) ∉ StatedScalars ι K → SolvableOrComponent H h

@[expose] def projMap (H : Subgroup (Matrix.GeneralLinearGroup ι K)) :
    H →* StatedProj H :=
  QuotientGroup.mk' ((StatedScalars ι K).subgroupOf H)

theorem projMap_surjective (H : Subgroup (Matrix.GeneralLinearGroup ι K)) :
    Function.Surjective (projMap H) := QuotientGroup.mk'_surjective _

theorem projMap_ker_le_center (H : Subgroup (Matrix.GeneralLinearGroup ι K)) :
    (projMap H).ker ≤ center H := by
  intro x hx
  rw [projMap, QuotientGroup.ker_mk', mem_subgroupOf] at hx
  rw [Subgroup.mem_center_iff]
  intro g
  have hx' : (x : Matrix.GeneralLinearGroup ι K) ∈ center (Matrix.GeneralLinearGroup ι K) := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact hx
  exact Subtype.ext (Subgroup.mem_center_iff.1 hx' g)

theorem mem_projMap_ker (H : Subgroup (Matrix.GeneralLinearGroup ι K)) (h : H) :
    h ∈ (projMap H).ker ↔ (h : Matrix.GeneralLinearGroup ι K) ∈ StatedScalars ι K := by
  rw [projMap, QuotientGroup.ker_mk', mem_subgroupOf]

theorem solvableOrComponent_of_matrixDichotomy {X : Type} [Group X]
    {H : Subgroup (Matrix.GeneralLinearGroup ι K)} (hd : MatrixDichotomy H)
    (e : X ≃* StatedProj H) (τ : X) (hτ : orderOf τ = 2) : SolvableOrComponent X τ := by
  refine solvableOrComponent_of_mulEquiv e τ ?_
  obtain ⟨h, hh⟩ := projMap_surjective H (e τ)
  have hτ2 : (e τ) ^ 2 = 1 := by
    rw [← map_pow, ← hτ, pow_orderOf_eq_one, map_one]
  have hτ1 : e τ ≠ 1 := by
    intro h1
    have := orderOf_eq_one_iff.2 (e.injective (h1.trans (map_one e).symm))
    rw [hτ] at this
    exact absurd this (by norm_num)
  have hsq : (h : Matrix.GeneralLinearGroup ι K) ^ 2 ∈ StatedScalars ι K := by
    have : h ^ 2 ∈ (projMap H).ker := by
      rw [MonoidHom.mem_ker, map_pow, hh]
      exact hτ2
    exact (mem_projMap_ker H _).1 this
  obtain ⟨u, hu⟩ := hsq
  have hns : (h : Matrix.GeneralLinearGroup ι K) ∉ StatedScalars ι K := by
    intro hmem
    exact hτ1 (hh ▸ ((MonoidHom.mem_ker).1 ((mem_projMap_ker H h).2 hmem)))
  have := solvableOrComponent_of_cover (projMap H) (projMap_surjective H)
    (projMap_ker_le_center H) h (hd h ⟨u, hu.symm⟩ hns)
  rwa [hh] at this

end Classical

end CFSG.ComponentClassification.CatFC.DS81
