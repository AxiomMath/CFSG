module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33C2FSpWit
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33C2LWit

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.L33.C2

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticFlag SymplecticHigher

variable {r : ℕ} {K : Type} [Field K]

abbrev spT (v : Fin r ⊕ Fin r → K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K :=
  vecMulVec v (formJ r K *ᵥ v)

abbrev spX (p q : Fin r ⊕ Fin r → K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K :=
  vecMulVec p (formJ r K *ᵥ q) + vecMulVec q (formJ r K *ᵥ p)

theorem spT_mul_self (h2 : (2 : K) = 0) (v : Fin r ⊕ Fin r → K) : spT v * spT v = 0 := by
  rw [vecMulVec_mul_vecMulVec, formJ_self h2, zero_smul, vecMulVec_zero]

theorem spT_iso (h2 : (2 : K) = 0) (v : Fin r ⊕ Fin r → K) :
    (1 + spT v)ᵀ * formJ r K * (1 + spT v) = formJ r K :=
  iso_one_add h2 (vecMulVec_transpose_mul (formJ_transpose h2) v) (spT_mul_self h2 v)

theorem spX_transpose_mul (h2 : (2 : K) = 0) (p q : Fin r ⊕ Fin r → K) :
    (spX p q)ᵀ * formJ r K = formJ r K * spX p q := by
  rw [transpose_add, transpose_vecMulVec, transpose_vecMulVec, add_mul, vecMulVec_mul,
    vecMulVec_mul, vecMul_eq_mulVec (formJ_transpose h2), vecMul_eq_mulVec (formJ_transpose h2),
    mul_add, mul_vecMulVec, mul_vecMulVec, add_comm]

theorem hasWit_sp_comm [NeZero r] [CharP K 2] {v : MulAut (StatedProj (StatedSp r K))}
    {Q : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K → Prop}
    (hfix : ∀ g : StatedSp r K, Q (spMat g) → v (proj r K g) = proj r K g)
    {x y m : Fin r ⊕ Fin r → K} (hxy : (formJ r K *ᵥ x) ⬝ᵥ y = 1)
    (hxm : (formJ r K *ᵥ x) ⬝ᵥ m = 0) (hym : (formJ r K *ᵥ y) ⬝ᵥ m = 0) (hm : m ≠ 0)
    (hQx : Q (1 + spT x)) (hQy : Q (1 + spT y)) (hQX : Q (1 + spX m x)) :
    HasWit v := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hJ := formJ_transpose (r := r) h2
  have hxx := formJ_self h2 x
  have hyy := formJ_self h2 y
  have hmm := formJ_self h2 m
  have hyx : (formJ r K *ᵥ y) ⬝ᵥ x = 1 := by rw [form_comm hJ]; exact hxy
  have hmx : (formJ r K *ᵥ m) ⬝ᵥ x = 0 := by rw [form_comm hJ]; exact hxm
  have hmy : (formJ r K *ᵥ m) ⬝ᵥ y = 0 := by rw [form_comm hJ]; exact hym
  set a := spT (r := r) x with ha
  set b := spT (r := r) y with hb
  have haa : a * a = 0 := spT_mul_self h2 x
  have hbb : b * b = 0 := spT_mul_self h2 y
  have hab : a * b = vecMulVec x (formJ r K *ᵥ y) := by
    rw [ha, hb, vecMulVec_mul_vecMulVec, hxy, one_smul]
  have hba : b * a = vecMulVec y (formJ r K *ᵥ x) := by
    rw [ha, hb, vecMulVec_mul_vecMulVec, hyx, one_smul]
  have haba : a * b * a = a := by rw [hab, ha, vecMulVec_mul_vecMulVec, hyx, one_smul]
  have hbab : b * a * b = b := by rw [hba, hb, vecMulVec_mul_vecMulVec, hxy, one_smul]
  set ta := spOf h2 (1 + a) (spT_iso h2 x) with hta
  set tb := spOf h2 (1 + b) (spT_iso h2 y) with htb
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
  set X := spX (r := r) m x with hX
  have hXX : X * X = 0 := by
    simp only [hX, spX, add_mul, mul_add, vecMulVec_mul_vecMulVec, hxm, hxx, hmm, hmx,
      zero_smul, vecMulVec_zero, add_zero]
  set y₀ := spOf h2 (1 + X) (iso_one_add h2 (spX_transpose_mul h2 m x) hXX) with hy₀
  have hy₀i : y₀⁻¹ = y₀ := inv_eq_of_mul_eq_one_right (spOf_mul_self h2 hXX _)
  have hbm : (1 + b) *ᵥ m = m := by
    rw [add_mulVec, one_mulVec, hb, vecMulVec_mulVec, hym, MulOpposite.op_zero, zero_smul,
      add_zero]
  have ham : (1 + a) *ᵥ m = m := by
    rw [add_mulVec, one_mulVec, ha, vecMulVec_mulVec, hxm, MulOpposite.op_zero, zero_smul,
      add_zero]
  have hbx : (1 + b) *ᵥ x = x + y := by
    rw [add_mulVec, one_mulVec, hb, vecMulVec_mulVec, hyx, MulOpposite.op_one, one_smul]
  have hax : (1 + a) *ᵥ (x + y) = y := by
    rw [add_mulVec, one_mulVec, ha, vecMulVec_mulVec, dotProduct_add, hxx, hxy, zero_add,
      MulOpposite.op_one, one_smul, add_comm x y, add_assoc, pi_add_self h2, add_zero]
  have hHm : spMat h *ᵥ m = m := by rw [hH, ← mulVec_mulVec, hbm, ham]
  have hHx : spMat h *ᵥ x = y := by rw [hH, ← mulVec_mulVec, hbx, hax]
  have hHH : spMat h * spMat h⁻¹ = 1 := spMat_mul_inv h
  have hconj : spMat h * X * spMat h⁻¹ = spX m y := by
    rw [hX, mul_add, add_mul, conj_vecMulVec (spMat_iso h) hHH,
      conj_vecMulVec (spMat_iso h) hHH, hHm, hHx]
  set M := spX (r := r) m y + X + spT m with hM
  have hc : spMat (h * y₀ * h⁻¹ * y₀⁻¹) = 1 + M := by
    rw [hy₀i, spMat_mul, spMat_mul, spMat_mul, hy₀, spMat_spOf,
      show spMat h * (1 + X) * spMat h⁻¹ * (1 + X) =
        (spMat h * spMat h⁻¹ + spMat h * X * spMat h⁻¹) * (1 + X) by noncomm_ring, hHH, hconj]
    have hXX' : spX (r := r) m y * X = spT m := by
      simp only [hX, spX, spT, add_mul, mul_add, vecMulVec_mul_vecMulVec, hym, hyx, hmm, hmx,
        zero_smul, one_smul, vecMulVec_zero, add_zero, zero_add]
    rw [show (1 + spX (r := r) m y) * (1 + X) = 1 + spX m y + X + spX m y * X by noncomm_ring,
      hXX', hM]
    abel
  refine hasWit_of_comm_sp h y₀ (m := 3) ⟨1, rfl⟩ h3 hc ?_ ?_ ?_ (hfix y₀ ?_)
  · simp only [hM, hX, spX, spT, add_mul, mul_add, vecMulVec_mul_vecMulVec, hxm, hxx, hmm, hmx,
      hym, hyy, hmy, hxy, hyx, zero_smul, one_smul, vecMulVec_zero, add_zero, zero_add]
    exact mat_add_self h2 _
  · intro hM0
    apply hm
    have h0 := congrArg (· *ᵥ x) hM0
    simp only [hM, hX, spX, spT, add_mulVec, vecMulVec_mulVec, hyx, hmx, hxx,
      MulOpposite.op_one, MulOpposite.op_zero, one_smul, zero_smul, add_zero, zero_mulVec] at h0
    exact h0
  · rw [hh, map_mul, map_mul, hfix ta (by rw [hta, spMat_spOf]; exact hQx),
      hfix tb (by rw [htb, spMat_spOf]; exact hQy)]
  · rw [hy₀, spMat_spOf]
    exact hQX

end CFSG.ComponentClassification.HarrisLit.L33.C2
