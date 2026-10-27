module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.Symplectic.Basic

public noncomputable section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.Symplectic

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial

variable {r : ℕ} {K : Type} [Field K]

theorem psf_neg_comm (x y : Fin r ⊕ Fin r → K) :
    pairedSympForm K r x y = -pairedSympForm K r y x := by
  simp only [pairedSympForm_apply]
  rw [dotProduct_comm (y ∘ Sum.inl), dotProduct_comm (y ∘ Sum.inr)]
  ring

theorem exists_dual {a : Fin r ⊕ Fin r → K} (ha : a ≠ 0) :
    ∃ z, pairedSympForm K r z a = 1 := by
  obtain ⟨x, hx⟩ := Function.ne_iff.1 ha
  rcases x with i | i
  · refine ⟨Pi.single (Sum.inr i) (-(a (Sum.inl i))⁻¹), ?_⟩
    rw [pairedSympForm_apply]
    simp [dotProduct, Pi.single_apply]
    exact inv_mul_cancel₀ hx
  · refine ⟨Pi.single (Sum.inl i) ((a (Sum.inr i))⁻¹), ?_⟩
    rw [pairedSympForm_apply]
    simp [dotProduct, Pi.single_apply]
    exact inv_mul_cancel₀ hx

theorem psf_eq_zero_of_eigen (g : StatedSp r K) {η η' : K} (h : η * η' ≠ 1)
    {x y : Fin r ⊕ Fin r → K} (hx : spMat g *ᵥ x = η • x) (hy : spMat g *ᵥ y = η' • y) :
    pairedSympForm K r x y = 0 := by
  have h1 := pairedSympForm_spMat_mulVec g x y
  simp only [hx, hy, map_smul, LinearMap.smul_apply, smul_eq_mul] at h1
  have h2 : (η * η' - 1) * pairedSympForm K r x y = 0 := by linear_combination h1
  rcases mul_eq_zero.1 h2 with h3 | h3
  · exact absurd (sub_eq_zero.1 h3) h
  · exact h3

theorem exists_eigen_dual (g : StatedSp r K) {p : ℕ} (hgp : g ^ p = 1) (hp : (p : K) ≠ 0) {η : K}
    (hη : η ^ p = 1) {a z : Fin r ⊕ Fin r → K} (ha : spMat g *ᵥ a = η⁻¹ • a)
    (hz : pairedSympForm K r z a = 1) :
    ∃ y, spMat g *ᵥ y = η • y ∧ pairedSympForm K r y a = 1 := by
  have hp0 : p ≠ 0 := fun h => hp (by simp [h])
  have hη0 : η ≠ 0 := by
    rintro rfl
    simp [zero_pow hp0] at hη
  set f : ℕ → (Fin r ⊕ Fin r → K) := fun j => (η⁻¹) ^ j • (spMat (g ^ j) *ᵥ z) with hf
  have hfp : f p = f 0 := by
    simp [hf, hgp, inv_pow, hη, spMat_one]
  have hsucc : ∀ j, spMat g *ᵥ f j = η • f (j + 1) := by
    intro j
    simp only [hf, mulVec_smul, mulVec_mulVec, ← spMat_mul, ← pow_succ', smul_smul]
    congr 1
    rw [pow_succ]
    field_simp
  set Y := ∑ j ∈ Finset.range p, f j with hY
  have hMY : spMat g *ᵥ Y = η • Y := by
    rw [hY, Matrix.mulVec_sum]
    simp_rw [hsucc]
    rw [← Finset.smul_sum]
    congr 1
    have h1 := Finset.sum_range_succ f p
    have h2 := Finset.sum_range_succ' f p
    rw [hfp] at h1
    exact add_right_cancel (h2.symm.trans h1)
  have hpow : ∀ j : ℕ, spMat (g ^ j) *ᵥ a = (η⁻¹) ^ j • a := by
    intro j
    induction j with
    | zero => simp [spMat_one]
    | succ j ih =>
      rw [pow_succ', spMat_mul, ← mulVec_mulVec, ih, mulVec_smul, ha, smul_smul, pow_succ]
  have hb : ∀ j : ℕ, pairedSympForm K r (spMat (g ^ j) *ᵥ z) a = η ^ j * pairedSympForm K r z a := by
    intro j
    have h1 := pairedSympForm_spMat_mulVec (g ^ j) z a
    rw [hpow j, map_smul, smul_eq_mul] at h1
    have : ((η⁻¹) ^ j) * pairedSympForm K r (spMat (g ^ j) *ᵥ z) a = pairedSympForm K r z a := h1
    rw [← this, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hη0, one_pow, one_mul]
  refine ⟨(p : K)⁻¹ • Y, ?_, ?_⟩
  · rw [mulVec_smul, hMY, smul_comm]
  · rw [map_smul, LinearMap.smul_apply, hY, map_sum, LinearMap.sum_apply]
    have : ∀ j ∈ Finset.range p, pairedSympForm K r (f j) a = 1 := by
      intro j _
      simp only [hf, map_smul, LinearMap.smul_apply, smul_eq_mul, hb, hz]
      rw [mul_one, ← mul_pow, inv_mul_cancel₀ hη0, one_pow]
    rw [Finset.sum_congr rfl this]
    simp [hp]

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.Symplectic
