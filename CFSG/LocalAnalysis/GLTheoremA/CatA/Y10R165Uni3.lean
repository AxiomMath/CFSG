module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Uni
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Sp2

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks

open CFSG.LieType.SeitzGeneration HyperBlocks CFSG.Open
open CFSG.RankThree.PartOne.KCOrthogonal (exists_coe_add_of_isCompl)
open scoped CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
variable (A : Subgroup (V ≃ₗ[F] V)) [Fintype A]
variable {p : ℕ} {σ : F →+* F}

abbrev InvariantSesq (B : V →ₛₗ[σ] V →ₗ[F] F) : Prop :=
  ∀ a : ↥A, ∀ u v : V, B ((a : V ≃ₗ[F] V) u) ((a : V ≃ₗ[F] V) v) = B u v

theorem blockSpace_sesq_nondegenerate (hp : p.Prime) (hpF : (p : F) ≠ 0)
    (hA : IsElemAbelian p A) {B : V →ₛₗ[σ] V →ₗ[F] F} (hB : InvariantSesq A B)
    (hBn : B.SeparatingLeft) (D : Hyperplane A p) :
    (B.domRestrict₁₂ (blockSpace A D.1) (blockSpace A D.1)).SeparatingLeft := by
  rw [LinearMap.separatingLeft_iff_linear_nontrivial]
  rintro ⟨x, hxU⟩ hx
  have hx' : ∀ y : ↥(blockSpace A D.1), B x (y : V) = 0 := fun y => by
    have h1 := congrFun (congrArg DFunLike.coe hx) y
    simpa only [LinearMap.domRestrict₁₂_apply, LinearMap.zero_apply] using h1
  have hx0 : x = 0 := by
    rw [LinearMap.separatingLeft_iff_linear_nontrivial] at hBn
    refine hBn x (LinearMap.ext fun v => ?_)
    obtain ⟨u, r, rfl⟩ := exists_coe_add_of_isCompl (isCompl_blockSpace_ker A hp hpF hA D) v
    have hr : (r : V) ∈ LinearMap.ker (projBlock A hp hpF hA D) := r.2
    have hxr : B x (r : V) = 0 := blockSpace_ker_sesq_orthogonal A hp hpF hA B hB D hxU hr
    have hxu : B x (u : V) = 0 := hx' ⟨u, u.2⟩
    rw [map_add, hxu, hxr, add_zero]
    rfl
  exact Subtype.ext hx0

theorem inf_orthogonalBilin_blockSpace_eq_bot (hp : p.Prime) (hpF : (p : F) ≠ 0)
    (hA : IsElemAbelian p A) {B : V →ₛₗ[σ] V →ₗ[F] F} (hB : InvariantSesq A B)
    (hrefl : B.IsRefl) (hBn : B.SeparatingLeft) (D : Hyperplane A p) :
    blockSpace A D.1 ⊓ Submodule.orthogonalBilin B (blockSpace A D.1) = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxU, hxW⟩
  have hnd := blockSpace_sesq_nondegenerate A hp hpF hA hB hBn D
  rw [LinearMap.separatingLeft_iff_linear_nontrivial] at hnd
  have hzero : (⟨x, hxU⟩ : ↥(blockSpace A D.1)) = 0 := by
    refine hnd ⟨x, hxU⟩ (LinearMap.ext fun y => ?_)
    rw [LinearMap.domRestrict₁₂_apply, LinearMap.zero_apply]
    exact hrefl.eq_zero ((Submodule.mem_orthogonalBilin.mp hxW) y.1 y.2)
  simpa using congrArg Subtype.val hzero

theorem orthogonalBilin_blockSpace_eq_ker (hp : p.Prime) (hpF : (p : F) ≠ 0)
    (hA : IsElemAbelian p A) {B : V →ₛₗ[σ] V →ₗ[F] F} (hB : InvariantSesq A B)
    (hrefl : B.IsRefl) (hBn : B.SeparatingLeft) (D : Hyperplane A p) :
    Submodule.orthogonalBilin B (blockSpace A D.1) =
      LinearMap.ker (projBlock A hp hpF hA D) := by
  refine le_antisymm ?_ ?_
  · intro v hv
    obtain ⟨u, r, hsum⟩ := exists_coe_add_of_isCompl (isCompl_blockSpace_ker A hp hpF hA D) v
    have hr : (r : V) ∈ LinearMap.ker (projBlock A hp hpF hA D) := r.2
    have hrW : (r : V) ∈ Submodule.orthogonalBilin B (blockSpace A D.1) := by
      rw [Submodule.mem_orthogonalBilin]
      intro n hn
      exact blockSpace_ker_sesq_orthogonal A hp hpF hA B hB D hn hr
    have huW : (u : V) ∈ Submodule.orthogonalBilin B (blockSpace A D.1) := by
      rw [Submodule.mem_orthogonalBilin]
      intro n hn
      have h1 : B n ((u : V) + (r : V)) = 0 := by
        rw [hsum]
        exact (Submodule.mem_orthogonalBilin.mp hv) n hn
      rw [map_add, (Submodule.mem_orthogonalBilin.mp hrW) n hn, add_zero] at h1
      exact h1
    have hu0 : (u : V) = 0 := by
      have hmem : (u : V) ∈ blockSpace A D.1 ⊓
          Submodule.orthogonalBilin B (blockSpace A D.1) := ⟨u.2, huW⟩
      rw [inf_orthogonalBilin_blockSpace_eq_bot A hp hpF hA hB hrefl hBn D] at hmem
      simpa using hmem
    rw [LinearMap.mem_ker, ← hsum, map_add, projBlock_apply_of_mem A hp hpF hA D u.2,
      LinearMap.mem_ker.mp hr, hu0, add_zero]
  · intro v hv
    rw [Submodule.mem_orthogonalBilin]
    intro n hn
    exact blockSpace_ker_sesq_orthogonal A hp hpF hA B hB D hn hv

theorem isCompl_blockSpace_orthogonalBilin (hp : p.Prime) (hpF : (p : F) ≠ 0)
    (hA : IsElemAbelian p A) {B : V →ₛₗ[σ] V →ₗ[F] F} (hB : InvariantSesq A B)
    (hrefl : B.IsRefl) (hBn : B.SeparatingLeft) (D : Hyperplane A p) :
    IsCompl (blockSpace A D.1) (Submodule.orthogonalBilin B (blockSpace A D.1)) := by
  rw [orthogonalBilin_blockSpace_eq_ker A hp hpF hA hB hrefl hBn D]
  exact isCompl_blockSpace_ker A hp hpF hA D

end CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks
