module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOModel
public import
  CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalInvolutionRepresentation

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.O

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBOrthogonalInvolutionRepresentation
  (conjugationHom_eq_one_iff)
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
  (orthogonal_geometry_tail_model_point_family_invariant)

variable {K : Type} [Field K] {d : ℕ}

theorem exists_gram (h2 : (2 : K) ≠ 0) (Q : QuadraticForm K (Fin d → K))
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) :
    ∃ R : GL (Fin d) K, (R : Matrix (Fin d) (Fin d) K)ᵀ = R ∧ ∀ v, oQ R v = Q v := by
  set B := QuadraticMap.polarBilin Q with hBdef
  set M : Matrix (Fin d) (Fin d) K := (2⁻¹ : K) • LinearMap.toMatrix₂' K B with hM
  have hB : ∀ v w, B v w = v ⬝ᵥ (LinearMap.toMatrix₂' K B *ᵥ w) := by
    intro v w
    rw [← Matrix.toLinearMap₂'_apply', Matrix.toLinearMap₂'_toMatrix']
  have hMv : ∀ v w, v ⬝ᵥ (M *ᵥ w) = 2⁻¹ * QuadraticMap.polar Q v w := by
    intro v w
    rw [hM, smul_mulVec, dotProduct_smul, smul_eq_mul, ← hB]
    rfl
  have hsym : Mᵀ = M := by
    ext i j
    rw [transpose_apply, hM, Matrix.smul_apply, Matrix.smul_apply, LinearMap.toMatrix₂'_apply,
      LinearMap.toMatrix₂'_apply]
    change 2⁻¹ • QuadraticMap.polar Q _ _ = 2⁻¹ • QuadraticMap.polar Q _ _
    rw [QuadraticMap.polar_comm]
  have hdet : M.det ≠ 0 := by
    intro h0
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    apply hv0
    refine hQ.1 v fun w => ?_
    change QuadraticMap.polar Q v w = 0
    rw [QuadraticMap.polar_comm]
    have := hMv w v
    rw [hv, dotProduct_zero] at this
    have e : (2 : K)⁻¹ * QuadraticMap.polar Q w v = 0 := this.symm
    exact (mul_eq_zero.1 e).resolve_left (inv_ne_zero h2)
  refine ⟨Matrix.nonsingInvUnit M (isUnit_iff_ne_zero.2 hdet), hsym, fun v => ?_⟩
  rw [oQ_apply]
  change v ⬝ᵥ M *ᵥ v = Q v
  rw [hMv, QuadraticMap.polar_self, two_smul]
  field_simp
  ring

variable {H : Type} [Group H] {n p f : ℕ}

theorem oKer_coordinateOdd (h : StatedClassicalModel H .POmegaOdd n p f) (K : Type) [Field K]
    [Finite K] (hK : Nat.card K = p ^ f)
    (e : H ≃* StatedProj (StatedOmega (StatedQuadOdd n K))) : OKer (coordinateQuadOdd n K) := by
  obtain ⟨-, hQ, hS, -⟩ := coordinate_model_witness_odd h K hK e
  intro g hg
  exact (conjugationHom_eq_one_iff _ hQ hS (coordinate_model_intrinsic_odd h K hK e).2.1.2.1
    g).1 hg

theorem oSurj_coordinateOdd (h : StatedClassicalModel H .POmegaOdd n p f) (K : Type) [Field K]
    [Finite K] (hK : Nat.card K = p ^ f)
    (e : H ≃* StatedProj (StatedOmega (StatedQuadOdd n K))) :
    OSurj (coordinateQuadOdd n K) := by
  have h1 := (orthogonal_geometry_tail_model_point_family_invariant H .POmegaOdd (Or.inl rfl) n
    p f h K hK).2
  have h2 := coordinate_odd_family_eq_matrixImage h K hK e
  intro α
  have hα : α ∈ matrixProjectiveImage (coordinateQuadOdd n K) := by
    rw [← h2, h1]
    trivial
  obtain ⟨g, hg⟩ := hα
  exact ⟨g, hg.symm⟩

end CFSG.ComponentClassification.Burgoyne.O
