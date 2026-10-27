module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointKernelBasic

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalPointKernel

open Matrix CatalogueBOrthogonalSemilinear CatalogueBOrthogonalPointData
open CatalogueBOrthogonalPointAction CatalogueBOrthogonalScalarKernel

universe u

variable {K : Type u} [Field K] {d : ℕ}

theorem similarityPointAction_kernel_actions (Q : QuadraticForm K (Fin d → K))
    (hQ : Q.polarBilin.Nondegenerate)
    (hS : ∃ S : Submodule K (Fin d → K),
      Module.finrank K S = 3 ∧ ∀ v ∈ S, Q v = 0)
    (g : similarityPairs Q) (hg : similarityPointAction Q g = 1) :
    g.val.right = 1 ∧ ∃ a : Kˣ,
      GeneralLinearGroup.scalar (Fin d) a = g.val.left ∧
      (∀ v, coordinateSemilinearMap g.val v = (a : K) • v) ∧
      (∀ v, coordinateSemilinearMap g.val⁻¹ v = (↑(a⁻¹) : K) • v) ∧
      (∀ c : K, g.val.right c = c) ∧ (multiplier Q g : K) = (a : K) ^ 2 := by
  obtain ⟨hfield, a, ha, hi, hmultiplier⟩ := scalar_kernel_actions hQ hS
    (coordinateSemilinearEquiv g.val) (multiplier Q g)
    (coordinateSemilinearEquiv_similarity Q g)
    ((similarityPointAction_eq_one_iff_lines Q g).mp hg)
  have hfield' : g.val.right = 1 := hfield
  refine ⟨hfield', a, scalarMatrix_eq_of_coordinateMap g.val hfield' a ha, ha, ?_,
    ?_, hmultiplier⟩
  · intro v
    rw [← coordinateSemilinearEquiv_symm_apply]
    exact hi v
  · intro c
    rw [hfield']
    rfl

theorem similarityPointAction_eq_one_iff (Q : QuadraticForm K (Fin d → K))
    (hQ : Q.polarBilin.Nondegenerate)
    (hS : ∃ S : Submodule K (Fin d → K),
      Module.finrank K S = 3 ∧ ∀ v ∈ S, Q v = 0)
    (g : similarityPairs Q) :
    similarityPointAction Q g = 1 ↔ g.val.right = 1 ∧
      ∃ a : Kˣ, GeneralLinearGroup.scalar (Fin d) a = g.val.left := by
  constructor
  · intro hg
    obtain ⟨hfield, a, ha, _, _, _, _⟩ := similarityPointAction_kernel_actions Q hQ hS g hg
    exact ⟨hfield, a, ha⟩
  · rintro ⟨hfield, a, ha⟩
    exact similarityPointAction_of_scalarMatrix Q g hfield a ha

theorem similarityPointAction_kernel_submodule (Q : QuadraticForm K (Fin d → K))
    (g : similarityPairs Q) (hg : similarityPointAction Q g = 1)
    (W : Submodule K (Fin d → K)) (hW : Module.finrank K W = 1)
    (hsing : ∀ v ∈ W, Q v = 0) :
    W.map (coordinateSemilinearLinearMap g.val) = W :=
  (similarityPointAction_eq_one_iff_lines Q g).mp hg W hW hsing

theorem similarityPointAction_inverse_kernel_submodule (Q : QuadraticForm K (Fin d → K))
    (g : similarityPairs Q) (hg : similarityPointAction Q g = 1)
    (W : Submodule K (Fin d → K)) (hW : Module.finrank K W = 1)
    (hsing : ∀ v ∈ W, Q v = 0) :
    W.map (coordinateSemilinearLinearMap g.val⁻¹) = W := by
  have hi : similarityPointAction Q g⁻¹ = 1 := by rw [map_inv, hg, inv_one]
  exact similarityPointAction_kernel_submodule Q g⁻¹ hi W hW hsing

end CFSG.ComponentClassification.CatalogueBOrthogonalPointKernel
