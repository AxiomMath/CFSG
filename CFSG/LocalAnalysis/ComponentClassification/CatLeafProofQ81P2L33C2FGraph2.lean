module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33C2FGraph

public section

namespace CFSG.ComponentClassification.HarrisLit.L33.C2

open CFSG Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {n : ℕ} {K : Type} [Field K]

theorem hasWit_graph_double (h2 : (2 : K) = 0) {A : GL (Fin n) K}
    {R : Matrix (Fin n) (Fin n) K} (hRA : ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = R)
    (hR : Rᵀ = R) {x₁ y₁ x₂ y₂ : Fin n → K}
    (x1x1 : (R *ᵥ x₁) ⬝ᵥ x₁ = 0) (x2x2 : (R *ᵥ x₂) ⬝ᵥ x₂ = 0)
    (y1y1 : (R *ᵥ y₁) ⬝ᵥ y₁ = 0) (y2y2 : (R *ᵥ y₂) ⬝ᵥ y₂ = 0)
    (x1y1 : (R *ᵥ x₁) ⬝ᵥ y₁ = 1) (x2y2 : (R *ᵥ x₂) ⬝ᵥ y₂ = 1)
    (x1x2 : (R *ᵥ x₁) ⬝ᵥ x₂ = 0) (x1y2 : (R *ᵥ x₁) ⬝ᵥ y₂ = 0)
    (y1x2 : (R *ᵥ y₁) ⬝ᵥ x₂ = 0) (y1y2 : (R *ᵥ y₁) ⬝ᵥ y₂ = 0) :
    HasWit (conjAut n K A * dualAut n K) := by
  have y1x1 : (R *ᵥ y₁) ⬝ᵥ x₁ = 1 := by rw [form_comm hR]; exact x1y1
  have y2x2 : (R *ᵥ y₂) ⬝ᵥ x₂ = 1 := by rw [form_comm hR]; exact x2y2
  have x2x1 : (R *ᵥ x₂) ⬝ᵥ x₁ = 0 := by rw [form_comm hR]; exact x1x2
  have y2x1 : (R *ᵥ y₂) ⬝ᵥ x₁ = 0 := by rw [form_comm hR]; exact x1y2
  have x2y1 : (R *ᵥ x₂) ⬝ᵥ y₁ = 0 := by rw [form_comm hR]; exact y1x2
  have y2y1 : (R *ᵥ y₂) ⬝ᵥ y₁ = 0 := by rw [form_comm hR]; exact y1y2
  set a := vecMulVec x₁ (R *ᵥ x₁) + vecMulVec x₂ (R *ᵥ x₂) with ha
  set b := vecMulVec y₁ (R *ᵥ y₁) + vecMulVec y₂ (R *ᵥ y₂) with hb
  have haa : a * a = 0 := by
    simp only [ha, add_mul, mul_add, vecMulVec_mul_vecMulVec, x1x1, x1x2, x2x1, x2x2,
      zero_smul, vecMulVec_zero, add_zero]
  have hbb : b * b = 0 := by
    simp only [hb, add_mul, mul_add, vecMulVec_mul_vecMulVec, y1y1, y1y2, y2y1, y2y2,
      zero_smul, vecMulVec_zero, add_zero]
  have hab : a * b = vecMulVec x₁ (R *ᵥ y₁) + vecMulVec x₂ (R *ᵥ y₂) := by
    simp only [ha, hb, add_mul, mul_add, vecMulVec_mul_vecMulVec, x1y1, x1y2, x2y1, x2y2,
      one_smul, zero_smul, vecMulVec_zero, add_zero, zero_add]
  have hba : b * a = vecMulVec y₁ (R *ᵥ x₁) + vecMulVec y₂ (R *ᵥ x₂) := by
    simp only [ha, hb, add_mul, mul_add, vecMulVec_mul_vecMulVec, y1x1, y1x2, y2x1, y2x2,
      one_smul, zero_smul, vecMulVec_zero, add_zero, zero_add]
  have haba : a * b * a = a := by
    rw [hab]
    simp only [ha, add_mul, mul_add, vecMulVec_mul_vecMulVec, y1x1, y1x2, y2x1, y2x2, one_smul,
      zero_smul, vecMulVec_zero, add_zero, zero_add]
  have hbab : b * a * b = b := by
    rw [hba]
    simp only [hb, add_mul, mul_add, vecMulVec_mul_vecMulVec, x1y1, x1y2, x2y1, x2y2, one_smul,
      zero_smul, vecMulVec_zero, add_zero, zero_add]
  set h := unipOf h2 a haa * unipOf h2 b hbb with hh
  have hH : (h : Matrix (Fin n) (Fin n) K) = (1 + a) * (1 + b) := by
    rw [hh, Matrix.SpecialLinearGroup.coe_mul, coe_unipOf, coe_unipOf]
  have h3 : h ^ 3 = 1 := by
    ext i j
    rw [Matrix.SpecialLinearGroup.coe_pow, hH,
      pow_three_of_rel (add_self_eq_zero_of_two h2) haa hbb haba hbab]
    rfl
  have hu : ∀ (X : Matrix (Fin n) (Fin n) K) (hX : X * X = 0),
      unipOf h2 X hX * unipOf h2 X hX = 1 := fun X hX => by
    ext i j
    rw [Matrix.SpecialLinearGroup.coe_mul, coe_unipOf, one_add_mul_self h2 hX]
    rfl
  have hinv : h⁻¹ = unipOf h2 b hbb * unipOf h2 a haa := by
    rw [hh, _root_.mul_inv_rev, inv_eq_of_mul_eq_one_right (hu b hbb),
      inv_eq_of_mul_eq_one_right (hu a haa)]
  have hHi : ((h⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (1 + b) * (1 + a) := by
    rw [hinv, Matrix.SpecialLinearGroup.coe_mul, coe_unipOf, coe_unipOf]
  obtain ⟨z, hz⟩ : ∃ z, z = x₁ + x₂ := ⟨_, rfl⟩
  have zz : (R *ᵥ z) ⬝ᵥ z = 0 := by
    simp only [hz, mulVec_add, add_dotProduct, dotProduct_add, x1x1, x1x2, x2x1, x2x2,
      add_zero]
  have zy1 : (R *ᵥ z) ⬝ᵥ y₁ = 1 := by
    simp only [hz, mulVec_add, add_dotProduct, x1y1, x2y1, add_zero]
  have zy2 : (R *ᵥ z) ⬝ᵥ y₂ = 1 := by
    simp only [hz, mulVec_add, add_dotProduct, x1y2, x2y2, zero_add]
  have x1z : (R *ᵥ x₁) ⬝ᵥ z = 0 := by simp only [hz, dotProduct_add, x1x1, x1x2, add_zero]
  have x2z : (R *ᵥ x₂) ⬝ᵥ z = 0 := by simp only [hz, dotProduct_add, x2x1, x2x2, add_zero]
  have y1z : (R *ᵥ y₁) ⬝ᵥ z = 1 := by simp only [hz, dotProduct_add, y1x1, y1x2, add_zero]
  have y2z : (R *ᵥ y₂) ⬝ᵥ z = 1 := by simp only [hz, dotProduct_add, y2x1, y2x2, zero_add]
  have hbz : b *ᵥ z = y₁ + y₂ := by
    simp only [hb, add_mulVec, vecMulVec_mulVec, y1z, y2z, MulOpposite.op_one, one_smul]
  have haz : a *ᵥ z = 0 := by
    simp only [ha, add_mulVec, vecMulVec_mulVec, x1z, x2z, MulOpposite.op_zero, zero_smul,
      add_zero]
  have haw : a *ᵥ (z + (y₁ + y₂)) = z := by
    simp only [ha, add_mulVec, vecMulVec_mulVec, dotProduct_add, x1z, x1y1, x1y2, x2z, x2y1,
      x2y2, zero_add, add_zero, MulOpposite.op_one, one_smul]
    exact hz.symm
  have hbz' : (1 + b) *ᵥ z = z + (y₁ + y₂) := by rw [add_mulVec, one_mulVec, hbz]
  have haz' : (1 + a) *ᵥ z = z := by rw [add_mulVec, one_mulVec, haz, add_zero]
  have hHz : (h : Matrix (Fin n) (Fin n) K) *ᵥ z = y₁ + y₂ := by
    rw [hH, ← mulVec_mulVec, hbz', add_mulVec, one_mulVec, haw, add_comm, ← add_assoc,
      vec_add_self_add h2]
  have hHiz : ((h⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ z =
      z + (y₁ + y₂) := by
    rw [hHi, ← mulVec_mulVec, haz', hbz']
  set E := vecMulVec z (R *ᵥ z) with hE
  have hEE : E * E = 0 := by
    rw [hE, vecMulVec_mul_vecMulVec, zz, zero_smul, vecMulVec_zero]
  have h11 : (1 : K) + 1 = 0 := by rw [one_add_one_eq_two, h2]
  have hne : (h : Matrix (Fin n) (Fin n) K) * E ≠ E * h := by
    refine mul_vecMulVec_ne (v := y₁) (φ := R *ᵥ x₁) zy1 x1z ?_
    rw [hHz, dotProduct_add, x1y1, x1y2, add_zero]
    exact one_ne_zero
  have haR : aᵀ * R = R * a := by
    rw [ha, transpose_add, add_mul, vecMulVec_transpose_mul hR, vecMulVec_transpose_mul hR,
      mul_add]
  have hbR : bᵀ * R = R * b := by
    rw [hb, transpose_add, add_mul, vecMulVec_transpose_mul hR, vecMulVec_transpose_mul hR,
      mul_add]
  have hvh : (conjAut n K A * dualAut n K) (proj n K h) = proj n K h := by
    rw [hh, map_mul, map_mul, graph_fix hRA (g := unipOf h2 a haa) (iso_one_add h2 haR haa),
      graph_fix hRA (g := unipOf h2 b hbb) (iso_one_add h2 hbR hbb)]
  refine hasWit_of_sl h2 h (m := 3) ⟨1, rfl⟩ h3 hEE ?_ ?_ hne hvh
    (graph_fix hRA (iso_one_add h2 (vecMulVec_transpose_mul hR z) hEE))
  · rw [hE, vecMulVec_mul_mul_self, hHz, dotProduct_add, zy1, zy2, h11, zero_smul]
  · rw [hE, vecMulVec_mul_mul_self, hHiz, dotProduct_add, zz, dotProduct_add, zy1, zy2, h11,
      zero_add, zero_smul]

end CFSG.ComponentClassification.HarrisLit.L33.C2
