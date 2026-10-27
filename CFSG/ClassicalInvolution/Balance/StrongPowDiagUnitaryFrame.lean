module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.ClassicalInvolution.ModelFacts.CommutingFundamentalLinear
public import CFSG.ClassicalInvolution.Models.UnitaryPairs.Frame

public section

namespace CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary

open Matrix Module CFSG.ClassicalInvolution.Models CFSG.ClassicalGroups.Unitary
  CFSG.LieType.Universal.Unitary CFSG.ClassicalInvolution.Phan
open CFSG.ClassicalInvolution.ModelFacts (exists_fibre_map)

variable {K : Type} [Field K] {σ : K ≃+* K} {n : ℕ}

theorem herm_eq_zero_of_eigen_mat {M : Matrix (Fin n) (Fin n) K} (hM : conjTr σ M * M = 1)
    {v w : Fin n → K} {a b : K} (hv : M *ᵥ v = a • v) (hw : M *ᵥ w = b • w)
    (hab : σ a * b ≠ 1) : herm σ v w = 0 := by
  have h := herm_mulVec (σ := σ) M v w
  rw [hM, one_mulVec, hv, hw, herm_smul_left, herm_smul_right, ← mul_assoc] at h
  have h' : (σ a * b - 1) * herm σ v w = 0 := by linear_combination h
  exact (mul_eq_zero.mp h').resolve_left (sub_ne_zero.mpr hab)

theorem exists_gu_frame_signs (hσ : IsUnitaryInvolution σ) (h2 : (2 : K) ≠ 0) (hn : 0 < n)
    {i₁ i₂ : Matrix (Fin n) (Fin n) K} (hu₁ : conjTr σ i₁ * i₁ = 1)
    (hu₂ : conjTr σ i₂ * i₂ = 1) (h₁ : i₁ * i₁ = 1) (h₂ : i₂ * i₂ = 1)
    (hc : i₁ * i₂ = i₂ * i₁) :
    ∃ (g : SUid σ n) (ε : Fin n → Bool × Bool),
      i₁ * suMat g = suMat g * Matrix.diagonal (fun j => signOf K (ε j).1) ∧
      i₂ * suMat g = suMat g * Matrix.diagonal (fun j => signOf K (ε j).2) := by
  have horth : ∀ s t : Bool × Bool, s ≠ t →
      Orth σ (jointEig i₁ i₂ s) (jointEig i₁ i₂ t) := by
    intro s t hst v hv w hw
    rw [mem_jointEig] at hv hw
    by_cases h1 : s.1 = t.1
    · have h2' : s.2 ≠ t.2 := fun h => hst (Prod.ext h1 h)
      exact herm_eq_zero_of_eigen_mat hu₂ hv.2 hw.2 (map_signOf_mul_signOf_ne_one h2 h2')
    · exact herm_eq_zero_of_eigen_mat hu₁ hv.1 hw.1 (map_signOf_mul_signOf_ne_one h2 h1)
  have hint := isInternal_jointEigenspace h2 (toLin'_mul_self h₁) (toLin'_mul_self h₂)
    (toLin'_mul_comm hc)
  have hsum : ∑ s, finrank K (jointEig i₁ i₂ s) = n := by
    have := finrank_eq_sum_of_isInternal (jointEig i₁ i₂) hint
    simpa using this.symm
  obtain ⟨ε, hε⟩ := exists_fibre_map (fun s => finrank K (jointEig i₁ i₂ s)) n hsum
  have hnd : ∀ s, Nondeg σ (jointEig i₁ i₂ s) := nondeg_of_orth_of_iSup_eq_top _
    (iSup_jointEigenspace h2 (toLin'_mul_self h₁) (toLin'_mul_self h₂) (toLin'_mul_comm hc))
    (fun s t hst => horth s t hst)
  obtain ⟨g, hg⟩ := exists_su_adapted hσ hn (jointEig i₁ i₂) hnd horth ε hε
  refine ⟨g, ε, ?_, ?_⟩
  · ext a j
    rw [Matrix.mul_diagonal]
    have := congr_fun (mem_jointEig.mp (hg j)).1 a
    rw [suMat_smul, Matrix.mulVec_single_one] at this
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm] using this
  · ext a j
    rw [Matrix.mul_diagonal]
    have := congr_fun (mem_jointEig.mp (hg j)).2 a
    rw [suMat_smul, Matrix.mulVec_single_one] at this
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm] using this

end CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary
