module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33C2FSpComm

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.L33.C2

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticFlag SymplecticHigher

variable {r : ℕ} {K : Type} [Field K]

theorem form_mulVec_left {N : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K}
    (hNJ : Nᵀ * formJ r K = formJ r K * N) (u w : Fin r ⊕ Fin r → K) :
    (formJ r K *ᵥ (N *ᵥ u)) ⬝ᵥ w = (formJ r K *ᵥ u) ⬝ᵥ (N *ᵥ w) := by
  rw [mulVec_mulVec, ← hNJ, ← mulVec_mulVec, mulVec_transpose, ← dotProduct_mulVec]

theorem hasWit_sp_dbl [NeZero r] [CharP K 2] {v : MulAut (StatedProj (StatedSp r K))}
    {Q : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K → Prop}
    (hfix : ∀ g : StatedSp r K, Q (spMat g) → v (proj r K g) = proj r K g)
    {N : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K} (hNJ : Nᵀ * formJ r K = formJ r K * N)
    (hNN : N * N = 0) {x y : Fin r ⊕ Fin r → K} (hbxx : (formJ r K *ᵥ x) ⬝ᵥ (N *ᵥ x) = 0)
    (hbyy : (formJ r K *ᵥ y) ⬝ᵥ (N *ᵥ y) = 0) (hbxy : (formJ r K *ᵥ x) ⬝ᵥ (N *ᵥ y) = 1)
    (hxy : (formJ r K *ᵥ x) ⬝ᵥ y = 0) (hQx : Q (1 + spX (N *ᵥ x) x))
    (hQy : Q (1 + spX (N *ᵥ y) y)) (hQE : Q (1 + spT (N *ᵥ x))) : HasWit v := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hJ := formJ_transpose (r := r) h2
  have hNNv : ∀ w, N *ᵥ (N *ᵥ w) = 0 := fun w => by rw [mulVec_mulVec, hNN, zero_mulVec]
  have hsa := form_mulVec_left hNJ
  have hxx := formJ_self h2 x
  have hyy := formJ_self h2 y
  have hyx : (formJ r K *ᵥ y) ⬝ᵥ x = 0 := by rw [form_comm hJ]; exact hxy
  have hbyx : (formJ r K *ᵥ y) ⬝ᵥ (N *ᵥ x) = 1 := by rw [← hsa, form_comm hJ, hbxy]
  have hNxNx : (formJ r K *ᵥ (N *ᵥ x)) ⬝ᵥ (N *ᵥ x) = 0 := formJ_self h2 _
  have hNyNy : (formJ r K *ᵥ (N *ᵥ y)) ⬝ᵥ (N *ᵥ y) = 0 := formJ_self h2 _
  have hNxNy : (formJ r K *ᵥ (N *ᵥ x)) ⬝ᵥ (N *ᵥ y) = 0 := by rw [hsa, hNNv, dotProduct_zero]
  have hNyNx : (formJ r K *ᵥ (N *ᵥ y)) ⬝ᵥ (N *ᵥ x) = 0 := by rw [hsa, hNNv, dotProduct_zero]
  have hNxy : (formJ r K *ᵥ (N *ᵥ x)) ⬝ᵥ y = 1 := by rw [hsa, hbxy]
  have hNyx : (formJ r K *ᵥ (N *ᵥ y)) ⬝ᵥ x = 1 := by rw [hsa, hbyx]
  have hNxx : (formJ r K *ᵥ (N *ᵥ x)) ⬝ᵥ x = 0 := by rw [hsa, hbxx]
  have hNyy : (formJ r K *ᵥ (N *ᵥ y)) ⬝ᵥ y = 0 := by rw [hsa, hbyy]
  set a := spX (r := r) (N *ᵥ x) x with ha
  set b := spX (r := r) (N *ᵥ y) y with hb
  have haa : a * a = 0 := by
    simp only [ha, spX, add_mul, mul_add, vecMulVec_mul_vecMulVec, hbxx, hxx, hNxNx, hNxx,
      zero_smul, vecMulVec_zero, add_zero]
  have hbb : b * b = 0 := by
    simp only [hb, spX, add_mul, mul_add, vecMulVec_mul_vecMulVec, hbyy, hyy, hNyNy, hNyy,
      zero_smul, vecMulVec_zero, add_zero]
  have hab : a * b = vecMulVec (N *ᵥ x) (formJ r K *ᵥ y) +
      vecMulVec x (formJ r K *ᵥ (N *ᵥ y)) := by
    simp only [ha, hb, spX, add_mul, mul_add, vecMulVec_mul_vecMulVec, hbxy, hxy, hNxNy, hNxy,
      zero_smul, one_smul, vecMulVec_zero, add_zero, zero_add]
  have hba : b * a = vecMulVec (N *ᵥ y) (formJ r K *ᵥ x) +
      vecMulVec y (formJ r K *ᵥ (N *ᵥ x)) := by
    simp only [ha, hb, spX, add_mul, mul_add, vecMulVec_mul_vecMulVec, hbyx, hyx, hNyNx, hNyx,
      zero_smul, one_smul, vecMulVec_zero, add_zero, zero_add]
  have haba : a * b * a = a := by
    rw [hab]
    simp only [ha, spX, add_mul, mul_add, vecMulVec_mul_vecMulVec, hbyx, hyx, hNyNx, hNyx,
      zero_smul, one_smul, vecMulVec_zero, add_zero, zero_add]
  have hbab : b * a * b = b := by
    rw [hba]
    simp only [hb, spX, add_mul, mul_add, vecMulVec_mul_vecMulVec, hbxy, hxy, hNxNy, hNxy,
      zero_smul, one_smul, vecMulVec_zero, add_zero, zero_add]
  set ta := spOf h2 (1 + a) (iso_one_add h2 (spX_transpose_mul h2 _ _) haa) with hta
  set tb := spOf h2 (1 + b) (iso_one_add h2 (spX_transpose_mul h2 _ _) hbb) with htb
  set h := ta * tb with hh
  have hH : spMat h = (1 + a) * (1 + b) := by rw [hh, spMat_mul, hta, htb, spMat_spOf, spMat_spOf]
  have h3 : h ^ 3 = 1 := by
    apply spMat_injective
    rw [pow_three', spMat_mul, spMat_mul, hH, spMat_one, ← pow_three',
      pow_three_of_rel (mat_add_self h2) haa hbb haba hbab]
  have hinv : h⁻¹ = tb * ta := by
    rw [hh, _root_.mul_inv_rev, inv_eq_of_mul_eq_one_right (spOf_mul_self h2 haa _),
      inv_eq_of_mul_eq_one_right (spOf_mul_self h2 hbb _)]
  have hHi : spMat h⁻¹ = (1 + b) * (1 + a) := by
    rw [hinv, spMat_mul, hta, htb, spMat_spOf, spMat_spOf]
  have hbNx : (1 + b) *ᵥ (N *ᵥ x) = N *ᵥ x + N *ᵥ y := by
    rw [add_mulVec, one_mulVec, hb, spX, add_mulVec, vecMulVec_mulVec, vecMulVec_mulVec, hbyx,
      hNyNx, MulOpposite.op_one, MulOpposite.op_zero, one_smul, zero_smul, add_zero]
  have haNx : (1 + a) *ᵥ (N *ᵥ x) = N *ᵥ x := by
    rw [add_mulVec, one_mulVec, ha, spX, add_mulVec, vecMulVec_mulVec, vecMulVec_mulVec, hbxx,
      hNxNx, MulOpposite.op_zero, zero_smul, zero_smul, add_zero, add_zero]
  have haNxy : (1 + a) *ᵥ (N *ᵥ x + N *ᵥ y) = N *ᵥ y := by
    rw [add_mulVec, one_mulVec, ha, spX, add_mulVec, vecMulVec_mulVec, vecMulVec_mulVec,
      dotProduct_add, dotProduct_add, hbxx, hbxy, hNxNx, hNxNy, zero_add, add_zero,
      MulOpposite.op_one, MulOpposite.op_zero, one_smul, zero_smul, add_zero, add_comm,
      ← add_assoc, pi_add_self h2, zero_add]
  have hHNx : spMat h *ᵥ (N *ᵥ x) = N *ᵥ y := by rw [hH, ← mulVec_mulVec, hbNx, haNxy]
  have hHiNx : spMat h⁻¹ *ᵥ (N *ᵥ x) = N *ᵥ x + N *ᵥ y := by
    rw [hHi, ← mulVec_mulVec, haNx, hbNx]
  set E := spT (r := r) (N *ᵥ x) with hE
  have hEE : E * E = 0 := spT_mul_self h2 _
  set u := spOf h2 (1 + E) (spT_iso h2 _) with hu
  refine hasWit_of_sp h u (m := 3) ⟨1, rfl⟩ h3 (E := E) (by rw [hu, spMat_spOf]) hEE ?_ ?_ ?_
    ?_ (hfix u (by rw [hu, spMat_spOf]; exact hQE))
  · rw [hE, vecMulVec_mul_mul_self, hHNx, hNxNy, zero_smul]
  · rw [hE, vecMulVec_mul_mul_self, hHiNx, dotProduct_add, hNxNx, hNxNy, add_zero, zero_smul]
  · refine mul_vecMulVec_ne (v := y) (φ := formJ r K *ᵥ x) hNxy hbxx ?_
    rw [hHNx, hbxy]
    exact one_ne_zero
  · rw [hh, map_mul, map_mul, hfix ta (by rw [hta, spMat_spOf]; exact hQx),
      hfix tb (by rw [htb, spMat_spOf]; exact hQy)]

end CFSG.ComponentClassification.HarrisLit.L33.C2
