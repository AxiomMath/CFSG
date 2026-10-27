module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOFieldDesc
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOBlock
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOEigen

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.O

open Matrix CFSG Subgroup
open CFSG.ComponentClassification.Burgoyne.PSL (diagGL coe_diagGL signMat reflGL reflGL_mem
  compInd commute_signMat_iff commute_compInd_iff)
open scoped commutatorElement

variable {K : Type} [Field K] {d : ℕ}

abbrev bil (w : Fin d → K) (v y : Fin d → K) : K := v ⬝ᵥ diagonal w *ᵥ y

theorem bil_comm (w : Fin d → K) (v y : Fin d → K) : bil w v y = bil w y v :=
  dot_symm (diagonal_transpose w) y v

theorem bil_eq_sum (w : Fin d → K) (v y : Fin d → K) : bil w v y = ∑ i, v i * w i * y i := by
  simp only [bil, dotProduct, mulVec_diagonal]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem matrix_ext_mulVec {M N : Matrix (Fin d) (Fin d) K} (h : ∀ y, M *ᵥ y = N *ᵥ y) :
    M = N := by
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  simpa only [mulVec_single_one, col_apply] using this

@[expose] def reflM (w : Fin d → K) (v : Fin d → K) : Matrix (Fin d) (Fin d) K :=
  1 - (2 / bil w v v) • vecMulVec v (fun j => w j * v j)

theorem reflM_mulVec (w : Fin d → K) (v y : Fin d → K) :
    reflM w v *ᵥ y = y - (2 / bil w v v * bil w v y) • v := by
  rw [reflM, sub_mulVec, one_mulVec, smul_mulVec, vecMulVec_mulVec, op_smul_eq_smul, smul_smul]
  congr 3
  rw [bil_eq_sum]
  simp only [dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem bil_smul_left (w : Fin d → K) (a : K) (v y : Fin d → K) :
    bil w (a • v) y = a * bil w v y := by
  rw [bil, smul_dotProduct, smul_eq_mul]

theorem bil_smul_right (w : Fin d → K) (a : K) (v y : Fin d → K) :
    bil w v (a • y) = a * bil w v y := by
  rw [bil, mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem bil_sub_left (w : Fin d → K) (v v' y : Fin d → K) :
    bil w (v - v') y = bil w v y - bil w v' y := by
  rw [bil, sub_dotProduct]

theorem bil_sub_right (w : Fin d → K) (v y y' : Fin d → K) :
    bil w v (y - y') = bil w v y - bil w v y' := by
  rw [bil, mulVec_sub, dotProduct_sub]

theorem reflM_mulVec_self (w : Fin d → K) {v : Fin d → K} (hv : bil w v v ≠ 0) :
    reflM w v *ᵥ v = -v := by
  rw [reflM_mulVec, div_mul_cancel₀ _ hv, two_smul]
  abel

theorem bil_reflM (w : Fin d → K) {v : Fin d → K} (hv : bil w v v ≠ 0) (y z : Fin d → K) :
    bil w (reflM w v *ᵥ y) (reflM w v *ᵥ z) = bil w y z := by
  rw [reflM_mulVec, reflM_mulVec, bil_sub_left, bil_sub_right, bil_sub_right, bil_smul_left,
    bil_smul_right, bil_smul_left, bil_smul_right, bil_comm w y v]
  field_simp
  ring

theorem reflM_reflM_mulVec (w : Fin d → K) {v : Fin d → K} (hv : bil w v v ≠ 0)
    (y : Fin d → K) : reflM w v *ᵥ (reflM w v *ᵥ y) = y := by
  have hb : bil w v (reflM w v *ᵥ y) = -bil w v y := by
    rw [reflM_mulVec, bil_sub_right, bil_smul_right]
    field_simp
    ring
  rw [reflM_mulVec w v (reflM w v *ᵥ y), hb, reflM_mulVec w v y,
    show 2 / bil w v v * -bil w v y = -(2 / bil w v v * bil w v y) by ring, neg_smul,
    sub_neg_eq_add, sub_add_cancel]

theorem reflM_mul_self (w : Fin d → K) {v : Fin d → K} (hv : bil w v v ≠ 0) :
    reflM w v * reflM w v = 1 := by
  refine matrix_ext_mulVec fun y => ?_
  rw [← mulVec_mulVec, reflM_reflM_mulVec w hv, one_mulVec]

theorem reflM_isometry (w : Fin d → K) {v : Fin d → K} (hv : bil w v v ≠ 0) :
    (reflM w v)ᵀ * diagonal w * reflM w v = diagonal w := by
  ext i j
  have e := bil_reflM w hv (Pi.single i 1) (Pi.single j 1)
  rw [bil, bil, dot_mulVec_mulVec] at e
  simpa only [single_one_dotProduct, mulVec_single_one, col_apply] using e

@[expose] def reflGLv (w : Fin d → K) {v : Fin d → K} (hv : bil w v v ≠ 0) : GL (Fin d) K :=
  ⟨reflM w v, reflM w v, reflM_mul_self w hv, reflM_mul_self w hv⟩

theorem coe_reflGLv (w : Fin d → K) {v : Fin d → K} (hv : bil w v v ≠ 0) :
    ((reflGLv w hv : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = reflM w v := rfl

theorem reflGLv_inv (w : Fin d → K) {v : Fin d → K} (hv : bil w v v ≠ 0) :
    (reflGLv w hv)⁻¹ = reflGLv w hv :=
  inv_eq_of_mul_eq_one_right (Units.ext (reflM_mul_self w hv))

theorem reflGLv_mem_oIsoBlock {w : Fin d → K} (hw : ∀ i, w i ≠ 0) {v : Fin d → K}
    (hv : bil w v v ≠ 0) {I : Finset (Fin d)} (hvI : ∀ i, i ∉ I → v i = 0) :
    reflGLv w hv ∈ oIsoBlock K hw I := by
  rw [mem_oIsoBlock_iff]
  refine ⟨(CatalogueBGraphForm.mem_isometryGroup _ _ _ _).2 (by
    rw [coe_reflGLv, coe_diagGL]; exact reflM_isometry w hv), fun i j hij => ?_⟩
  rw [coe_reflGLv, reflM, Matrix.sub_apply, Matrix.smul_apply, vecMulVec_apply, one_apply]
  rcases hij with hi | hj
  · rw [hvI i hi]
    simp
  · rw [hvI j hj]
    simp

theorem conj_reflM (w : Fin d → K) (v : Fin d → K) {g : GL (Fin d) K}
    (hg : (g : Matrix (Fin d) (Fin d) K)ᵀ * diagonal w * g = diagonal w) :
    (g : Matrix (Fin d) (Fin d) K) * reflM w v * ((g⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      reflM w ((g : Matrix (Fin d) (Fin d) K) *ᵥ v) := by
  have hbil : ∀ a b, bil w ((g : Matrix (Fin d) (Fin d) K) *ᵥ a)
      ((g : Matrix (Fin d) (Fin d) K) *ᵥ b) = bil w a b := by
    intro a b
    rw [bil, bil, dot_mulVec_mulVec, hg]
  have hgg : ∀ y, (g : Matrix (Fin d) (Fin d) K) *ᵥ
      (((g⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ y) = y := by
    intro y
    rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
  refine matrix_ext_mulVec fun y => ?_
  rw [← mulVec_mulVec, ← mulVec_mulVec, reflM_mulVec, mulVec_sub, mulVec_smul, hgg,
    reflM_mulVec, hbil v v]
  congr 3
  rw [← hbil v, hgg]

theorem reflM_single (w : Fin d → K) {b : Fin d} (hb : w b ≠ 0) :
    reflM w (Pi.single b 1) = signMat K {b} := by
  have hq : bil w (Pi.single b 1) (Pi.single b 1) = w b := by
    rw [bil_eq_sum, Finset.sum_eq_single b (fun i _ hi => by simp [hi])
      (by simp)]
    simp
  ext i j
  rw [reflM, hq, Matrix.sub_apply, Matrix.smul_apply, vecMulVec_apply, one_apply, signMat,
    diagonal_apply, smul_eq_mul]
  by_cases hij : i = j
  · subst hij
    by_cases hib : i = b
    · subst hib
      simp only [Pi.single_eq_same, Finset.mem_singleton, ↓reduceIte, mul_one]
      field_simp
      ring
    · simp [hib]
  · by_cases hib : i = b
    · subst hib
      simp [hij, Ne.symm hij]
    · simp [hij, hib]

theorem reflM_sub_mulVec (h2 : (2 : K) ≠ 0) (w : Fin d → K) {a c : Fin d → K}
    (hac : bil w a a = bil w c c)
    (hv : bil w (a - c) (a - c) ≠ 0) : reflM w (a - c) *ᵥ a = c := by
  have e : bil w (a - c) (a - c) = 2 * bil w (a - c) a := by
    rw [bil_sub_left, bil_sub_right, bil_sub_right, bil_sub_left, bil_comm w c a, ← hac]
    ring
  rw [reflM_mulVec, e]
  have h' : bil w (a - c) a ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at e
    exact hv e
  rw [show 2 / (2 * bil w (a - c) a) * bil w (a - c) a = 1 by field_simp, one_smul]
  abel

theorem exists_smul_of_commute_reflM (h2 : (2 : K) ≠ 0) (w : Fin d → K) {u : Fin d → K}
    (hu : bil w u u ≠ 0) {D : Matrix (Fin d) (Fin d) K}
    (hD : D * reflM w u = reflM w u * D) : ∃ κ : K, D *ᵥ u = κ • u := by
  have e : reflM w u *ᵥ (D *ᵥ u) = -(D *ᵥ u) := by
    rw [mulVec_mulVec, ← hD, ← mulVec_mulVec, reflM_mulVec_self w hu, mulVec_neg]
  rw [reflM_mulVec] at e
  set z := D *ᵥ u with hz
  set κ := 2 / bil w u u * bil w u z with hκ
  refine ⟨bil w u z / bil w u u, ?_⟩
  have e2 : (2 : K) • z = κ • u := by
    rw [two_smul]
    have : z - κ • u + z = 0 := by rw [e, neg_add_cancel]
    rw [← sub_eq_zero, ← this]
    abel
  have e3 : z = (2 : K)⁻¹ • ((2 : K) • z) := by
    rw [smul_smul, inv_mul_cancel₀ h2, one_smul]
  conv_lhs => rw [e3, e2]
  rw [smul_smul, hκ]
  congr 1
  field_simp

end CFSG.ComponentClassification.Burgoyne.O
