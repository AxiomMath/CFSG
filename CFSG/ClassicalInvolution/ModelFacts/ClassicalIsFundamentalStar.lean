module

public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalLinear

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open Matrix

section Ring

variable {R : Type*} [Ring R] {e f : R}

theorem star_partOn_mul_partOn (σ : R →+ R) (hσ : ∀ a b, σ (a * b) = σ b * σ a)
    (hef : e + f = 1) (hef0 : e * f = 0) (hfe : f * e = 0) (hσe : σ e = e) (hσf : σ f = f)
    {x : R} (hxe : x * e = e * x) (hx : σ x * x = 1) :
    σ (partOn e f x) * partOn e f x = 1 := by
  have he := idem_left hef hef0
  have hf' := idem_right hef hfe
  unfold partOn
  rw [map_add, hσ, hσ, hσe, hσf]
  calc (e * (σ x * e) + f) * (e * x * e + f)
      = e * σ x * (e * e) * x * e + e * σ x * (e * f) + (f * e) * x * e + f * f := by noncomm_ring
    _ = e * σ x * e * x * e + 0 + 0 + f := by rw [he, hef0, hfe, hf']; simp
    _ = e * (σ x * x) * (e * e) + f := by
        have h3 : e * σ x * e * x * e = e * (σ x * x) * (e * e) := by
          calc e * σ x * e * x * e = e * σ x * (e * x) * e := by noncomm_ring
            _ = e * σ x * (x * e) * e := by rw [← hxe]
            _ = e * (σ x * x) * (e * e) := by noncomm_ring
        rw [h3]
        simp
    _ = e + f := by rw [hx, mul_one, he, he]
    _ = 1 := hef

theorem fixes_comm (σ : R →+ R) (hσ : ∀ a b, σ (a * b) = σ b * σ a) (hσf : σ f = f)
    {x : R} (hxf : x * f = f) (hx : σ x * x = 1) : f * x = f := by
  have h1 : f * σ x = f := by
    have := congrArg σ hxf
    rwa [hσ, hσf] at this
  calc f * x = (f * σ x) * x := by rw [h1]
    _ = f * (σ x * x) := mul_assoc _ _ _
    _ = f := by rw [hx, mul_one]

end Ring

section Proj

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {F : Type*} [Field F]

@[expose] noncomputable def eMinus (D : Matrix ι ι F) : Matrix ι ι F := (2 : F)⁻¹ • (1 - D)

@[expose] noncomputable def ePlus (D : Matrix ι ι F) : Matrix ι ι F := (2 : F)⁻¹ • (1 + D)

variable {D : Matrix ι ι F}

omit [Fintype ι] in
theorem eMinus_add_ePlus (h2 : (2 : F) ≠ 0) : eMinus D + ePlus D = 1 := by
  unfold eMinus ePlus
  rw [← smul_add]
  have : (1 - D) + (1 + D) = (2 : F) • (1 : Matrix ι ι F) := by
    rw [two_smul]; abel
  rw [this, smul_smul, inv_mul_cancel₀ h2, one_smul]

theorem eMinus_mul_ePlus (hD : D * D = 1) : eMinus D * ePlus D = 0 := by
  unfold eMinus ePlus
  rw [smul_mul_smul_comm]
  have : (1 - D) * (1 + D) = 0 := by
    have h : (1 - D) * (1 + D) = 1 - D * D := by noncomm_ring
    rw [h, hD, sub_self]
  rw [this, smul_zero]

theorem ePlus_mul_eMinus (hD : D * D = 1) : ePlus D * eMinus D = 0 := by
  unfold eMinus ePlus
  rw [smul_mul_smul_comm]
  have : (1 + D) * (1 - D) = 0 := by
    have h : (1 + D) * (1 - D) = 1 - D * D := by noncomm_ring
    rw [h, hD, sub_self]
  rw [this, smul_zero]

omit [Fintype ι] in
theorem eq_ePlus_sub_eMinus (h2 : (2 : F) ≠ 0) : D = ePlus D - eMinus D := by
  unfold eMinus ePlus
  rw [← smul_sub]
  have : (1 + D) - (1 - D) = (2 : F) • D := by rw [two_smul]; abel
  rw [this, smul_smul, inv_mul_cancel₀ h2, one_smul]

omit [Fintype ι] in
theorem one_add_eq_smul_ePlus (h2 : (2 : F) ≠ 0) :
    (1 : Matrix ι ι F) + D = (2 : F) • ePlus D := by
  unfold ePlus
  rw [smul_smul, mul_inv_cancel₀ h2, one_smul]

omit [Fintype ι] in
theorem one_sub_eq_smul_eMinus (h2 : (2 : F) ≠ 0) :
    (1 : Matrix ι ι F) - D = (2 : F) • eMinus D := by
  unfold eMinus
  rw [smul_smul, mul_inv_cancel₀ h2, one_smul]

theorem commute_eMinus' {x : Matrix ι ι F} (hx : x * D = D * x) :
    x * eMinus D = eMinus D * x := by
  unfold eMinus
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
    Matrix.one_mul, hx]

theorem commute_ePlus' {x : Matrix ι ι F} (hx : x * D = D * x) :
    x * ePlus D = ePlus D * x := by
  unfold ePlus
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
    Matrix.one_mul, hx]

theorem commute_of_commute_ePlus {x : Matrix ι ι F} (h2 : (2 : F) ≠ 0)
    (hx : x * ePlus D = ePlus D * x) : x * D = D * x := by
  have h1 : D = (2 : F) • ePlus D - 1 := by
    rw [← one_add_eq_smul_ePlus h2]; abel
  rw [h1, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, hx, Matrix.mul_one,
    Matrix.one_mul]

theorem mul_ePlus (hD : D * D = 1) : D * ePlus D = ePlus D := by
  unfold ePlus
  rw [Matrix.mul_smul, Matrix.mul_add, Matrix.mul_one, hD, add_comm]

theorem mul_eMinus (hD : D * D = 1) : D * eMinus D = -eMinus D := by
  unfold eMinus
  rw [Matrix.mul_smul, Matrix.mul_sub, Matrix.mul_one, hD, ← smul_neg, neg_sub]

theorem ePlus_mulVec_of_mulVec_eq {v : ι → F} (h2 : (2 : F) ≠ 0) (hv : D.mulVec v = v) :
    (ePlus D).mulVec v = v := by
  unfold ePlus
  rw [Matrix.smul_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, hv, ← two_smul F v, smul_smul,
    inv_mul_cancel₀ h2, one_smul]

theorem eMinus_mulVec_of_mulVec_eq {v : ι → F} (h2 : (2 : F) ≠ 0) (hv : D.mulVec v = -v) :
    (eMinus D).mulVec v = v := by
  unfold eMinus
  rw [Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, hv, sub_neg_eq_add,
    ← two_smul F v, smul_smul, inv_mul_cancel₀ h2, one_smul]

theorem commute_of_commute_eMinus {x : Matrix ι ι F} (h2 : (2 : F) ≠ 0)
    (hx : x * eMinus D = eMinus D * x) : x * D = D * x := by
  have h1 : D = 1 - (2 : F) • eMinus D := by
    rw [← one_sub_eq_smul_eMinus h2]; abel
  rw [h1, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, hx, Matrix.mul_one,
    Matrix.one_mul]

end Proj

end CFSG.ClassicalInvolution.ModelFacts
