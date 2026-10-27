module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33C2FForm

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.L33.C2

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticFlag SymplecticHigher

variable {r : ℕ} {K : Type} [Field K]

theorem neg_one_matrix {ι : Type} [Fintype ι] [DecidableEq ι] (h2 : (2 : K) = 0) :
    (-1 : Matrix ι ι K) = 1 :=
  neg_eq_of_add_eq_zero_right (mat_add_self h2 1)

theorem formJ_transpose (h2 : (2 : K) = 0) : (formJ r K)ᵀ = formJ r K := by
  rw [formJ, fromBlocks_transpose, transpose_zero, transpose_one, transpose_neg, transpose_one,
    neg_one_matrix h2]

theorem formJ_mul_self (h2 : (2 : K) = 0) : formJ r K * formJ r K = 1 := by
  rw [formJ, fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.mul_one, zero_add, add_zero, neg_one_matrix h2]
  exact fromBlocks_one

theorem formJ_det_ne_zero (h2 : (2 : K) = 0) : (formJ r K).det ≠ 0 := by
  intro h0
  have := congrArg Matrix.det (formJ_mul_self (r := r) h2)
  rw [det_mul, h0, zero_mul, det_one] at this
  exact zero_ne_one this

theorem formJ_self (h2 : (2 : K) = 0) (x : Fin r ⊕ Fin r → K) : (formJ r K *ᵥ x) ⬝ᵥ x = 0 := by
  rw [form_self_eq h2 (formJ_transpose h2) (d := 0) (fun i => by
    rcases i with i | i <;> simp [formJ]), zero_dotProduct, mul_zero]

abbrev spMat (g : StatedSp r K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K :=
  ((g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)

theorem spMat_mul (g h : StatedSp r K) : spMat (g * h) = spMat g * spMat h :=
  rfl

theorem spMat_one : spMat (1 : StatedSp r K) = 1 :=
  rfl

theorem spMat_injective : Function.Injective (spMat (r := r) (K := K)) :=
  fun _ _ h => SymplecticTorusWeyl.statedSp_ext h

theorem spMat_iso (g : StatedSp r K) : (spMat g)ᵀ * formJ r K * spMat g = formJ r K :=
  SymplecticTorusWeyl.mem_statedSp_iff.mp g.2

theorem spMat_mul_inv (g : StatedSp r K) : spMat g * spMat g⁻¹ = 1 := by
  rw [← spMat_mul, mul_inv_cancel, spMat_one]

@[expose] def spOf (h2 : (2 : K) = 0) (T : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)
    (hT : Tᵀ * formJ r K * T = formJ r K) : StatedSp r K :=
  ⟨((Matrix.isUnit_iff_isUnit_det T).mpr
      (by rw [det_eq_one_of_iso h2 (formJ_det_ne_zero h2) hT]; exact isUnit_one)).unit,
    SymplecticTorusWeyl.mem_statedSp_iff.mpr (by rw [IsUnit.unit_spec]; exact hT)⟩

@[simp]
theorem spMat_spOf (h2 : (2 : K) = 0) (T : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)
    (hT : Tᵀ * formJ r K * T = formJ r K) : spMat (spOf h2 T hT) = T :=
  IsUnit.unit_spec _

theorem spOf_mul_self (h2 : (2 : K) = 0) {X : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K}
    (hXX : X * X = 0) (hT : (1 + X)ᵀ * formJ r K * (1 + X) = formJ r K) :
    spOf h2 (1 + X) hT * spOf h2 (1 + X) hT = 1 := by
  apply spMat_injective
  rw [spMat_mul, spMat_spOf, spMat_one, show (1 + X) * (1 + X) = 1 + (X + X) + X * X by
    noncomm_ring, mat_add_self h2, hXX, add_zero, add_zero]

theorem conj_vecMulVec {H H' : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K}
    (hH : Hᵀ * formJ r K * H = formJ r K) (hHH' : H * H' = 1) (p q : Fin r ⊕ Fin r → K) :
    H * vecMulVec p (formJ r K *ᵥ q) * H' = vecMulVec (H *ᵥ p) (formJ r K *ᵥ (H *ᵥ q)) := by
  have hT : H'ᵀ * formJ r K = formJ r K * H := by
    calc H'ᵀ * formJ r K = H'ᵀ * (Hᵀ * formJ r K * H) := by rw [hH]
      _ = (H * H')ᵀ * formJ r K * H := by simp only [transpose_mul, Matrix.mul_assoc]
      _ = formJ r K * H := by rw [hHH', transpose_one, Matrix.one_mul]
  rw [mul_vecMulVec, vecMulVec_mul, ← mulVec_transpose, mulVec_mulVec, hT, ← mulVec_mulVec]

theorem hasWit_of_comm_sp [NeZero r] [CharP K 2] {v : MulAut (StatedProj (StatedSp r K))}
    (h y : StatedSp r K) {m : ℕ} (hm : Odd m) (hhm : h ^ m = 1)
    {M : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K} (hc : spMat (h * y * h⁻¹ * y⁻¹) = 1 + M)
    (hMM : M * M = 0) (hM0 : M ≠ 0) (hvh : v (proj r K h) = proj r K h)
    (hvy : v (proj r K y) = proj r K y) : HasWit v := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  set c := h * y * h⁻¹ * y⁻¹ with hcdef
  have hcc : c * c = 1 := by
    apply spMat_injective
    rw [spMat_mul, hc, spMat_one, show (1 + M) * (1 + M) = 1 + (M + M) + M * M by noncomm_ring,
      mat_add_self h2, hMM, add_zero, add_zero]
  have hc1 : c ≠ 1 := by
    intro h1
    apply hM0
    have := congrArg spMat h1
    rw [hc, spMat_one] at this
    simpa using this
  have hinj := (UnitaryHigher.proj_bijective_of_charTwo (r := r) (K := K)).1
  have hord : orderOf (proj r K c) = 2 := by
    rw [orderOf_injective (proj r K) hinj c]
    exact orderOf_eq_prime (by rw [sq, hcc]) hc1
  refine ⟨proj r K h, proj r K y, hvh, hvy, ?_, ?_⟩
  · exact hm.of_dvd_nat (orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hhm, map_one]))
  · have e : proj r K h * proj r K y * (proj r K h)⁻¹ * (proj r K y)⁻¹ = proj r K c := by
      rw [hcdef]
      simp only [map_mul, map_inv]
    rw [e, hord]

theorem hasWit_of_sp [NeZero r] [CharP K 2] {v : MulAut (StatedProj (StatedSp r K))}
    (h y : StatedSp r K) {m : ℕ} (hm : Odd m) (hhm : h ^ m = 1)
    {E : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K} (hy : spMat y = 1 + E) (hEE : E * E = 0)
    (hEh : E * spMat h * E = 0) (hEh' : E * spMat h⁻¹ * E = 0)
    (hne : spMat h * E ≠ E * spMat h) (hvh : v (proj r K h) = proj r K h)
    (hvy : v (proj r K y) = proj r K y) : HasWit v := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  obtain ⟨H, hH⟩ : ∃ H, H = spMat h := ⟨_, rfl⟩
  obtain ⟨H', hH'⟩ : ∃ H', H' = spMat h⁻¹ := ⟨_, rfl⟩
  rw [← hH] at hEh hne
  rw [← hH'] at hEh'
  have hHH' : H * H' = 1 := by rw [hH, hH', spMat_mul_inv]
  have hH'H : H' * H = 1 := by rw [hH, hH', ← spMat_mul, inv_mul_cancel, spMat_one]
  have hyy : y * y = 1 := by
    apply spMat_injective
    rw [spMat_mul, hy, spMat_one, show (1 + E) * (1 + E) = 1 + (E + E) + E * E by noncomm_ring,
      mat_add_self h2, hEE, add_zero, add_zero]
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hyy
  refine hasWit_of_comm_sp h y hm hhm (M := H * E * H' + E) ?_ ?_ ?_ hvh hvy
  · rw [hyi, spMat_mul, spMat_mul, spMat_mul, hy, ← hH, ← hH',
      show H * (1 + E) * H' * (1 + E) = H * H' + H * E * H' + E * 1 + H * (E * H' * E) - E +
        (H * H') * E by noncomm_ring, hHH', hEh', Matrix.mul_zero, add_zero, Matrix.mul_one,
      Matrix.one_mul]
    abel
  · rw [show (H * E * H' + E) * (H * E * H' + E) = H * (E * (H' * H) * E) * H' +
        H * (E * H' * E) + (E * H * E) * H' + E * E by noncomm_ring]
    simp only [hH'H, Matrix.mul_one, hEE, hEh, hEh', Matrix.mul_zero, Matrix.zero_mul, add_zero]
  · intro hM0
    apply hne
    have hconj : H * E * H' = E := by
      calc H * E * H' = H * E * H' + (E + E) := by rw [mat_add_self h2, add_zero]
        _ = (H * E * H' + E) + E := by abel
        _ = E := by rw [hM0, zero_add]
    calc H * E = H * E * (H' * H) := by rw [hH'H, Matrix.mul_one]
      _ = (H * E * H') * H := by simp only [Matrix.mul_assoc]
      _ = E * H := by rw [hconj]

end CFSG.ComponentClassification.HarrisLit.L33.C2
