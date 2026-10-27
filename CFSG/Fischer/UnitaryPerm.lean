module

public import CFSG.Fischer.UnitaryPts
import all CFSG.Fischer.F4

public section

namespace CFSG.Fischer

open CFSG.F4.Native Matrix CFSG.Sporadic.Th CFSG.Sporadic.Th.Native

attribute [local irreducible] CFSG.F4.Native.uPts ptIdx uVec

theorem hermStd_mulVec (g : GU0) (x y : W) :
    hermStd (((g : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4).mulVec x)
      (((g : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4).mulVec y) = hermStd x y := by
  have := g.2 x y
  rwa [herm_eq_std, herm_eq_std] at this

theorem mulVec_ne_zero (g : GL (Fin 6) F4) {w : W} (hw : w ≠ 0) :
    (g : Matrix (Fin 6) (Fin 6) F4).mulVec w ≠ 0 := by
  intro h
  apply hw
  have : ((g⁻¹ : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4).mulVec
      ((g : Matrix (Fin 6) (Fin 6) F4).mulVec w) = w := by
    rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
  rw [← this, h, mulVec_zero]

theorem ptIdx_mulVec_lt (g : GU0) (i : Fin 693) :
    ptIdx (((g : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4).mulVec (uVec i)) < 693 :=
  ptIdx_lt ptsFacts (mulVec_ne_zero _ (uVec_ne_zero ptsFacts i.2))
    (by rw [hermStd_mulVec]; exact uVec_iso ptsFacts i.2)

@[expose] def ptAct (g : GU0) (i : Fin 693) : Fin 693 :=
  ⟨ptIdx (((g : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4).mulVec (uVec i)), ptIdx_mulVec_lt g i⟩

theorem ptIdx_mulVec_normV (M : Matrix (Fin 6) (Fin 6) F4) {w : W} (hw : w ≠ 0) :
    ptIdx (M.mulVec (normV w)) = ptIdx (M.mulVec w) := by
  obtain ⟨c, hc, hcw⟩ := normV_eq_smul hw
  rw [hcw, mulVec_smul, ptIdx_smul hc]

theorem ptAct_val (g : GU0) (i : Fin 693) :
    (ptAct g i).val = ptIdx (((g : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4).mulVec (uVec i)) :=
  rfl

instance ptAction : MulAction GU0 (Fin 693) where
  smul := ptAct
  one_smul i := by
    change ptAct 1 i = i
    apply Fin.ext
    rw [ptAct_val, OneMemClass.coe_one, Units.val_one, one_mulVec, ptIdx_uVec ptsFacts i.2]
  mul_smul g h i := by
    change ptAct (g * h) i = ptAct g (ptAct h i)
    apply Fin.ext
    have hw := mulVec_ne_zero (h : GL (Fin 6) F4) (uVec_ne_zero ptsFacts i.2)
    have hiso : hermStd (((h : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4).mulVec (uVec i))
        (((h : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4).mulVec (uVec i)) = 0 := by
      rw [hermStd_mulVec]; exact uVec_iso ptsFacts i.2
    rw [ptAct_val, ptAct_val, ptAct_val, uVec_ptIdx ptsFacts hw hiso, ptIdx_mulVec_normV _ hw,
      Subgroup.coe_mul, Units.val_mul, ← mulVec_mulVec]

theorem smul_val (g : GU0) (i : Fin 693) :
    (g • i).val = ptIdx (((g : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4).mulVec (uVec i)) :=
  ptAct_val g i

private theorem sq_add' : ∀ a b : F4, (a + b) ^ 2 = a ^ 2 + b ^ 2 := by decide

private theorem conj_mul' : ∀ a b : F4, (a * b ^ 2) ^ 2 = b * a ^ 2 := by decide

private theorem add_self' : ∀ a : F4, a + a = 0 := by decide

theorem hermStd_add_left (x y z : W) : hermStd (x + y) z = hermStd x z + hermStd y z := by
  simp only [hermStd, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem hermStd_smul_left (c : F4) (x z : W) : hermStd (c • x) z = c * hermStd x z := by
  simp only [hermStd, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

theorem hermStd_add_right (x y z : W) : hermStd x (y + z) = hermStd x y + hermStd x z := by
  simp only [hermStd, Pi.add_apply, sq_add', mul_add, Finset.sum_add_distrib]

theorem hermStd_smul_right (c : F4) (x z : W) : hermStd x (c • z) = c ^ 2 * hermStd x z := by
  simp only [hermStd, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_pow]
  exact Finset.sum_congr rfl fun i _ => by ring

private theorem sum_sq (f : Fin 6 → F4) : (∑ i, f i) ^ 2 = ∑ i, f i ^ 2 := by
  simp only [Fin.sum_univ_six, sq_add']

theorem hermStd_swap (x y : W) : hermStd y x = (hermStd x y) ^ 2 := by
  unfold hermStd
  rw [sum_sq]
  exact Finset.sum_congr rfl fun i _ => (conj_mul' (x i) (y i)).symm

@[expose] def tvM (v : W) : Matrix (Fin 6) (Fin 6) F4 :=
  1 + replicateCol Unit v * replicateRow Unit (fun j => v j ^ 2)

theorem tvM_mulVec (v x : W) : (tvM v).mulVec x = x + hermStd x v • v := by
  funext i
  rw [tvM, Matrix.add_mulVec, one_mulVec, Pi.add_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  congr 1
  simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply, replicateCol_apply,
    replicateRow_apply, hermStd, Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by simp; ring

theorem tvM_mul_self {v : W} (hv : hermStd v v = 0) : tvM v * tvM v = 1 := by
  rw [Matrix.ext_iff_mulVec]
  intro x
  rw [← mulVec_mulVec, tvM_mulVec, tvM_mulVec, one_mulVec, hermStd_add_left,
    hermStd_smul_left, hv, mul_zero, add_zero, add_assoc, ← add_smul, add_self', zero_smul,
    add_zero]

theorem det_tvM {v : W} (hv : hermStd v v = 0) : (tvM v).det = 1 := by
  rw [tvM, det_one_add_replicateCol_mul_replicateRow]
  have : (fun j => v j ^ 2) ⬝ᵥ v = hermStd v v := by
    simp only [dotProduct, hermStd]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [this, hv, add_zero]

theorem isIsom_tvM {v : W} (hv : hermStd v v = 0) : IsIsom (tvM v) := by
  intro x y
  rw [herm_eq_std, herm_eq_std, tvM_mulVec, tvM_mulVec, hermStd_add_left, hermStd_add_right,
    hermStd_add_right, hermStd_smul_left, hermStd_smul_left, hermStd_smul_right,
    hermStd_smul_right, hv, hermStd_swap y v]
  have : hermStd x v * hermStd y v ^ 2 + hermStd x v * hermStd y v ^ 2 = 0 := add_self' _
  linear_combination this

@[expose] def tvGL (v : W) (hv : hermStd v v = 0) : GL (Fin 6) F4 :=
  ⟨tvM v, tvM v, tvM_mul_self hv, tvM_mul_self hv⟩

theorem tvGL_val (v : W) (hv : hermStd v v = 0) :
    ((tvGL v hv : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) = tvM v := rfl

theorem tvGL_mem_SU0 {v : W} (hv : hermStd v v = 0) : tvGL v hv ∈ SU0 := by
  rw [mem_SU0]
  refine ⟨?_, ?_⟩
  · apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, tvGL_val, det_tvM hv, Units.val_one]
  · rw [tvGL_val]
    exact isIsom_tvM hv

@[expose] def tvGU (v : W) (hv : hermStd v v = 0) : GU0 :=
  ⟨tvGL v hv, SU0_le_GU0 (tvGL_mem_SU0 hv)⟩

theorem uPos_get {m : ℕ} (hm : m < 4096) : uPos[m]! = uPts.toList.idxOf m := by
  unfold uPos
  rw [getElem!_pos _ m (by simpa using hm), Array.getElem_ofFn]

theorem uPos_get_le {m : ℕ} (hm : m < 4096) : uPos[m]! ≤ 693 := by
  rw [uPos_get hm, ← ptsFacts.size, ← Array.length_toList]
  exact List.idxOf_le_length

theorem ap_tvTable (c : ℕ) {i : ℕ} (hi : i < 693) {m : ℕ}
    (hm : normC (tvC c uPts[i]!) = m) (hm4 : m < 4096) :
    ap (tvTable c) i = uPts.toList.idxOf m := by
  unfold ap tvTable
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn, hm, UInt32.toNat_ofNat',
    Nat.mod_eq_of_lt (lt_of_le_of_lt (uPos_get_le hm4) (by norm_num)), uPos_get hm4]

theorem rep_tvTable (v : W) (hv : hermStd v v = 0) :
    Rep 693 (tvTable (codeOf v)) (tvGU v hv) := by
  intro i hi
  rw [idx_of_lt _ hi, smul_val]
  have hw : normC (tvC (codeOf v) uPts[i]!) =
      normC (codeOf (uVec i + hermStd (uVec i) v • v)) := by
    rw [← codeOf_uVec ptsFacts hi, tvC_codeOf]
  rw [ap_tvTable (codeOf v) hi hw (by rw [normC_codeOf]; exact codeOf_lt _)]
  show _ = ptIdx ((tvM v).mulVec (uVec i))
  rw [tvM_mulVec]
  unfold ptIdx
  rfl

end CFSG.Fischer
