module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.Symplectic.Basic

public noncomputable section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.Symplectic

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial

variable {r : ℕ} {K : Type} [Field K]

theorem exists_statedSp_of_frame (c : Fin r ⊕ Fin r → (Fin r ⊕ Fin r → K))
    (h : ∀ x y, pairedSympForm K r (c x) (c y) =
      (fromBlocks (0 : Matrix (Fin r) (Fin r) K) 1 (-1) 0) x y) :
    ∃ g : StatedSp r K, ∀ x, spMat g *ᵥ (Pi.single x 1) = c x := by
  set J : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K := fromBlocks 0 1 (-1) 0 with hJdef
  set G : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K := Matrix.of fun y x => c x y with hG
  have hGJ : Gᵀ * J * G = J := by
    ext x y
    have h1 := h x y
    have h2 : pairedSympForm K r (c x) (c y) = (Gᵀ * J * G) x y := by
      simp only [pairedSympForm, Matrix.toBilin'_apply', Matrix.mul_apply, Matrix.mulVec,
        dotProduct, hG, Matrix.of_apply, Matrix.transpose_apply, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      ring
    rw [← h2, h1]
  have hdet : IsUnit G.det := by
    have h3 := congrArg Matrix.det hGJ
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at h3
    have hJu : IsUnit J.det := by
      rw [hJdef, CFSG.ClassicalGroups.Symplectic.blueprintGram_eq_neg_J, Matrix.det_neg]
      exact (isUnit_neg_one.pow _).mul (Matrix.isUnit_det_J (Fin r) K)
    have : IsUnit (G.det * J.det * G.det) := by
      rw [h3]; exact hJu
    exact (isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_left this))
  let g : GL (Fin r ⊕ Fin r) K := Matrix.GeneralLinearGroup.mk'' G hdet
  have hgm : (g : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = G := rfl
  have hmem : g ∈ StatedSp r K := by
    rw [SymplecticTorusWeyl.mem_statedSp_iff, hgm]; exact hGJ
  refine ⟨⟨g, hmem⟩, fun x => ?_⟩
  ext y
  simp [spMat, hgm, hG, ]

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.Symplectic
