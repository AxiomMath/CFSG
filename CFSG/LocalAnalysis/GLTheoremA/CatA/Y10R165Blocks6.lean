module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Blocks5
public import Mathlib.LinearAlgebra.QuadraticForm.Basic

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks

open CFSG.Open
open CFSG.RankThree.PartOne.KCOrthogonal (exists_coe_add_of_isCompl)
open scoped CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
variable (A : Subgroup (V ≃ₗ[F] V)) [Fintype A]
variable {p : ℕ}

theorem blockEnd_quadratic (hp : p.Prime) (hpF : (p : F) ≠ 0) (hA : IsElemAbelian p A)
    (Q : QuadraticMap F V F) (hQ : ∀ a : ↥A, ∀ v : V, Q ((a : V ≃ₗ[F] V) v) = Q v)
    (t : Hyperplane A p → ↥A) (ht : ∀ D, t D ∉ D.1) (D : Hyperplane A p) (v : V) :
    Q (blockEnd A hp hpF hA t ht D v) = Q v := by
  have hB : ∀ a : ↥A, ∀ u v : V,
      QuadraticMap.polarBilin Q ((a : V ≃ₗ[F] V) u) ((a : V ≃ₗ[F] V) v)
        = QuadraticMap.polarBilin Q u v := by
    intro a u v
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polarBilin_apply_apply,
      QuadraticMap.polar, QuadraticMap.polar, ← (a : V ≃ₗ[F] V).map_add u v,
      hQ a (u + v), hQ a u, hQ a v]
  obtain ⟨u, r, rfl⟩ :=
    exists_coe_add_of_isCompl (isCompl_blockSpace_ker A hp hpF hA D) v
  have hu : (t D : V ≃ₗ[F] V) (u : V) ∈ blockSpace A D.1 :=
    blockSpace_invariant A hp hpF hA (a := t D) u.2
  have hmap : blockEnd A hp hpF hA t ht D ((u : V) + (r : V)) =
      (t D : V ≃ₗ[F] V) (u : V) + (r : V) := by
    rw [map_add, blockEnd_apply_mem A hp hpF hA t ht D u.2,
      blockEnd_apply_of_ker A hp hpF hA t ht D r.2]
  have hcross : QuadraticMap.polar Q ((t D : V ≃ₗ[F] V) (u : V)) (r : V) = 0 := by
    have h := blockSpace_ker_orthogonal A hp hpF hA (QuadraticMap.polarBilin Q) hB D hu r.2
    simpa only [QuadraticMap.polarBilin_apply_apply] using h
  have hcross' : QuadraticMap.polar Q (u : V) (r : V) = 0 := by
    have h := blockSpace_ker_orthogonal A hp hpF hA (QuadraticMap.polarBilin Q) hB D u.2 r.2
    simpa only [QuadraticMap.polarBilin_apply_apply] using h
  rw [hmap, QuadraticMap.map_add Q, QuadraticMap.map_add Q, hQ (t D) (u : V),
    hcross, hcross', add_zero]

end CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks
