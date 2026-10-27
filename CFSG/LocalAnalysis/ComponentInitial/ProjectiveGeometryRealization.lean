module

public import CFSG.LocalAnalysis.ComponentInitial.ProjectiveGeometryCoordinates
public import CFSG.LocalAnalysis.ComponentInitial.ProjectiveGeometryInfinity

public section

namespace CFSG.LocalAnalysis.ComponentInitial

namespace ProjectiveGeometry

open Matrix Module LinearFlag

variable {K : Type*} [Field K] {n : ℕ}

theorem semilinear_realization (hn : 3 ≤ n) (f : Point n K ≃ Point n K)
    (h : Hyperplane n K ≃ Hyperplane n K)
    (hfh : ∀ (L : Point n K) (H : Hyperplane n K),
      (L : Submodule K (Fin n → K)) ≤ H ↔ (f L : Submodule K (Fin n → K)) ≤ h H) :
    ∃ (A : GL (Fin n) K) (σ : K ≃+* K),
      (∀ L : Point n K, (f L : Submodule K (Fin n → K)) =
        (coordImage σ (L : Submodule K (Fin n → K))).map
          (mulVecLin (A : Matrix (Fin n) (Fin n) K))) ∧
      ∀ H : Hyperplane n K, (h H : Submodule K (Fin n → K)) =
        (coordImage σ (H : Submodule K (Fin n → K))).map
          (mulVecLin (A : Matrix (Fin n) (Fin n) K)) := by
  obtain ⟨d, rfl⟩ : ∃ d, n = d + 1 := ⟨n - 1, by omega⟩
  obtain ⟨Φ, ⟨hΦL, hΦH⟩, -⟩ := incidence_lattice f h hfh
  obtain ⟨A, Ψ, hΨ, hΨe, hΨ1⟩ := frame_normalization Φ
  obtain ⟨σ, hσ⟩ := coordinate_map_field (by omega : 2 ≤ d) Ψ hΨe hΨ1
  have hΨσ := infinity_extension σ Ψ hσ (affine_coordinates Ψ hΨe hΨ1).1
  have hΦ : ∀ W, Φ W =
      (coordImage σ W).map (mulVecLin (A : Matrix (Fin (d + 1)) (Fin (d + 1)) K)) :=
    fun W => by rw [← hΨσ, hΨ, map_mulVecLin_map_inv]
  exact ⟨A, σ, fun L => by rw [← hΦL, hΦ], fun H => by rw [← hΦH, hΦ]⟩

end ProjectiveGeometry

end CFSG.LocalAnalysis.ComponentInitial
