module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33C2FForm
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33C2LInner3

public section

namespace CFSG.ComponentClassification.HarrisLit.L33.C2

open CFSG Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {n : ℕ} {K : Type} [Field K]

theorem graph_fix {A : GL (Fin n) K} {R : Matrix (Fin n) (Fin n) K}
    (hRA : ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = R)
    {g : SpecialLinearGroup (Fin n) K} (hg : (g : Matrix (Fin n) (Fin n) K)ᵀ * R * g = R) :
    (conjAut n K A * dualAut n K) (proj n K g) = proj n K g :=
  conjAut_dualAut_proj_of_transpose_mul_mul A g (by rw [hRA]; exact hg)

theorem vec_add_self_add (h2 : (2 : K) = 0) (x y : Fin n → K) : x + x + y = y := by
  rw [vec_add_self h2, zero_add]

theorem hasWit_graph_torus [Finite K] (h2 : (2 : K) = 0) {A : GL (Fin n) K}
    {R : Matrix (Fin n) (Fin n) K} (hRA : ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = R)
    (hR : Rᵀ = R) {x y : Fin n → K} (hxx : (R *ᵥ x) ⬝ᵥ x = 0) (hyy : (R *ᵥ y) ⬝ᵥ y = 0)
    (hxy : (R *ᵥ x) ⬝ᵥ y = 1) {l : K} (hl0 : l ≠ 0) (hl1 : l ≠ 1) :
    HasWit (conjAut n K A * dualAut n K) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hRdet : R.det ≠ 0 := by
    rw [← hRA]
    exact (Matrix.isUnits_det_units A⁻¹).ne_zero
  have hyx : (R *ᵥ y) ⬝ᵥ x = 1 := by rw [form_comm hR]; exact hxy
  set P := vecMulVec x (R *ᵥ y) with hP
  set Q := vecMulVec y (R *ᵥ x) with hQ
  have hPP : P * P = P := by rw [hP, vecMulVec_mul_vecMulVec, hyx, one_smul]
  have hQQ : Q * Q = Q := by rw [hQ, vecMulVec_mul_vecMulVec, hxy, one_smul]
  have hPQ : P * Q = 0 := by
    rw [hP, hQ, vecMulVec_mul_vecMulVec, hyy, zero_smul, vecMulVec_zero]
  have hQP : Q * P = 0 := by
    rw [hP, hQ, vecMulVec_mul_vecMulVec, hxx, zero_smul, vecMulVec_zero]
  set I₀ := 1 - P - Q with hI₀
  have h00 : I₀ * I₀ = I₀ := by
    rw [hI₀, show (1 - P - Q) * (1 - P - Q) = 1 - P - Q - P + P * P + P * Q - Q + Q * P + Q * Q
      by noncomm_ring, hPP, hQQ, hPQ, hQP]
    abel
  have h0P : I₀ * P = 0 := by
    rw [hI₀, sub_mul, sub_mul, one_mul, hPP, hQP, sub_self, sub_zero]
  have hP0 : P * I₀ = 0 := by
    rw [hI₀, mul_sub, mul_sub, mul_one, hPP, hPQ, sub_self, sub_zero]
  have h0Q : I₀ * Q = 0 := by
    rw [hI₀, sub_mul, sub_mul, one_mul, hPQ, hQQ, sub_zero, sub_self]
  have hQ0 : Q * I₀ = 0 := by
    rw [hI₀, mul_sub, mul_sub, mul_one, hQP, hQQ, sub_zero, sub_self]
  set D : K → K → Matrix (Fin n) (Fin n) K := fun β γ => I₀ + β • P + γ • Q with hD
  have hDmul : ∀ β γ β' γ', D β γ * D β' γ' = D (β * β') (γ * γ') := fun β γ β' γ' => by
    simp only [hD, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, h00, h0P, hP0, h0Q, hQ0,
      hPP, hQQ, hPQ, hQP, smul_zero, add_zero, zero_add, smul_smul]
    rw [mul_comm β' β, mul_comm γ' γ]
  have hD1 : D 1 1 = 1 := by
    simp only [hD, one_smul, hI₀]
    abel
  have hDpow : ∀ β γ (m : ℕ), D β γ ^ m = D (β ^ m) (γ ^ m) := fun β γ m => by
    induction m with
    | zero => rw [pow_zero, pow_zero, pow_zero, hD1]
    | succ m ih => rw [pow_succ, ih, hDmul, ← pow_succ, ← pow_succ]
  have hPT : Pᵀ * R = R * Q := by
    rw [hP, hQ, transpose_vecMulVec, vecMulVec_mul, vecMul_eq_mulVec hR, mul_vecMulVec]
  have hQT : Qᵀ * R = R * P := by
    rw [hP, hQ, transpose_vecMulVec, vecMulVec_mul, vecMul_eq_mulVec hR, mul_vecMulVec]
  have hDT : ∀ β γ, (D β γ)ᵀ * R = R * D γ β := fun β γ => by
    simp only [hD, hI₀, transpose_add, transpose_sub, transpose_smul, transpose_one, add_mul,
      sub_mul, smul_mul_assoc, one_mul, hPT, hQT, mul_add, mul_sub, mul_smul_comm, mul_one]
    abel
  have hiso : ∀ β γ, β * γ = 1 → (D β γ)ᵀ * R * D β γ = R := fun β γ hβγ => by
    rw [hDT, Matrix.mul_assoc, hDmul, mul_comm γ β, hβγ, hD1, Matrix.mul_one]
  set τ := isoSL h2 hRdet (D l l⁻¹) (hiso l l⁻¹ (mul_inv_cancel₀ hl0)) with hτ
  set τ' := isoSL h2 hRdet (D l⁻¹ l) (hiso l⁻¹ l (inv_mul_cancel₀ hl0)) with hτ'
  have hττ' : τ * τ' = 1 := by
    ext i j
    rw [Matrix.SpecialLinearGroup.coe_mul, hτ, hτ', coe_isoSL, coe_isoSL, hDmul,
      mul_inv_cancel₀ hl0, inv_mul_cancel₀ hl0, hD1]
    rfl
  have hinv : τ⁻¹ = τ' := inv_eq_of_mul_eq_one_right hττ'
  have hev := (FiniteField.even_card_iff_char_two (F := K)).mp (ringChar_eq_two h2)
  have hK2 : 2 ≤ Fintype.card K := Fintype.one_lt_card
  have hm : Odd (Fintype.card K - 1) := Nat.odd_iff.mpr (by omega)
  have hτm : τ ^ (Fintype.card K - 1) = 1 := by
    ext i j
    rw [Matrix.SpecialLinearGroup.coe_pow, hτ, coe_isoSL, hDpow,
      FiniteField.pow_card_sub_one_eq_one l hl0,
      FiniteField.pow_card_sub_one_eq_one _ (inv_ne_zero hl0), hD1]
    rfl
  set E := vecMulVec x (R *ᵥ x) with hE
  have hEE : E * E = 0 := by
    rw [hE, vecMulVec_mul_vecMulVec, hxx, zero_smul, vecMulVec_zero]
  have hPE : P * E = E := by rw [hP, hE, vecMulVec_mul_vecMulVec, hyx, one_smul]
  have hQE : Q * E = 0 := by
    rw [hQ, hE, vecMulVec_mul_vecMulVec, hxx, zero_smul, vecMulVec_zero]
  have hEP : E * P = 0 := by
    rw [hP, hE, vecMulVec_mul_vecMulVec, hxx, zero_smul, vecMulVec_zero]
  have hEQ : E * Q = E := by rw [hQ, hE, vecMulVec_mul_vecMulVec, hxy, one_smul]
  have hDE : ∀ β γ, D β γ * E = β • E := fun β γ => by
    simp only [hD, hI₀, add_mul, sub_mul, one_mul, smul_mul_assoc, hPE, hQE, sub_self,
      smul_zero, add_zero, zero_add]
  have hED : ∀ β γ, E * D β γ = γ • E := fun β γ => by
    simp only [hD, hI₀, mul_add, mul_sub, mul_one, mul_smul_comm, hEP, hEQ, sub_self,
      sub_zero, smul_zero, add_zero, zero_add]
  have hne : (τ : Matrix (Fin n) (Fin n) K) * E ≠ E * τ := by
    rw [hτ, coe_isoSL, hDE, hED]
    intro heq
    have h := congrArg (fun X => (R *ᵥ y) ⬝ᵥ (X *ᵥ y)) heq
    simp only [smul_mulVec, hE, vecMulVec_mulVec, hxy, MulOpposite.op_one, one_smul,
      dotProduct_smul, hyx, smul_eq_mul, mul_one] at h
    apply hl1
    have hll : l * l = 1 := by
      calc l * l = l * l⁻¹ := by rw [← h]
        _ = 1 := mul_inv_cancel₀ hl0
    have h0 : (l - 1) * (l - 1) = 0 := by
      rw [show (l - 1) * (l - 1) = l * l - 2 * l + 1 by ring, hll, h2, zero_mul, sub_zero,
        one_add_one_eq_two, h2]
    exact sub_eq_zero.mp (mul_self_eq_zero.mp h0)
  refine hasWit_of_sl h2 τ hm hτm hEE ?_ ?_ hne
    (graph_fix hRA (hiso l l⁻¹ (mul_inv_cancel₀ hl0))) ?_
  · rw [hτ, coe_isoSL, hED, smul_mul_assoc, hEE, smul_zero]
  · rw [hinv, hτ', coe_isoSL, hED, smul_mul_assoc, hEE, smul_zero]
  · exact graph_fix hRA (iso_one_add h2 (vecMulVec_transpose_mul hR x) hEE)

end CFSG.ComponentClassification.HarrisLit.L33.C2
