module

public import CFSG.GH74.GLS.LU.Local.FiveStdMat5

public section

namespace CFSG.GH74.GLS.LU.Local.FiveStd.Mat

open CFSG.GH74.L5U5 CFSG.GH74.GLS.Stage2.Final.ModelBlock Matrix

variable {F : Type} [Field F] [CharP F 5]

omit [CharP F 5] in
theorem yGL_mat : ((yGL F : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = blk4 (-1) 1 := by
  rw [yGL, coe_diagGL]
  simp

omit [CharP F 5] in
theorem xyGL_mat : ((xyGL F : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = blk4 1 (-1) := by
  rw [xyGL, coe_diagGL]
  simp

theorem mat4_comm_y_false {x : E} (hs : x.s = false) :
    (mat4 x : Matrix (Fin 4) (Fin 4) F) * blk4 (-1) 1 = blk4 (-1) 1 * mat4 x := by
  simp only [mat4, hs, Bool.false_eq_true, ↓reduceIte, Matrix.mul_one]
  rw [blk4_mul, blk4_mul]
  simp

theorem mat4_comm_y_true {x : E} (hs : x.s = true) :
    (mat4 x : Matrix (Fin 4) (Fin 4) F) * blk4 (-1) 1 = -(blk4 (-1) 1 * mat4 x) := by
  simp only [mat4, hs, ↓reduceIte]
  rw [Matrix.mul_assoc, wMat_mul_blk4, ← Matrix.mul_assoc, ← Matrix.mul_assoc, blk4_mul, blk4_mul, ← Matrix.neg_mul]
  congr 1
  rw [← blk4_neg]
  simp

theorem glE_comm_y {x : E} (hx : validE x = true) :
    ∃ ε : Fˣ, glE x * yGL F = Matrix.GeneralLinearGroup.scalar (Fin 4) ε * (yGL F * glE x) := by
  cases hs : x.s
  · refine ⟨1, Units.ext ?_⟩
    rw [Units.val_mul, Units.val_mul, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, coe_glE hx, yGL_mat]
    rw [mat4_comm_y_false hs, scalar_mul_mat, Units.val_one, one_smul]
  · refine ⟨-1, Units.ext ?_⟩
    rw [Units.val_mul, Units.val_mul, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, coe_glE hx, yGL_mat]
    rw [mat4_comm_y_true hs, scalar_mul_mat, Units.val_neg, Units.val_one, neg_one_smul]

omit [CharP F 5] in
theorem inv_mul_scalar_mul (u : Fˣ) (P : GL (Fin 4) F) :
    P⁻¹ * (Matrix.GeneralLinearGroup.scalar (Fin 4) u * P) = Matrix.GeneralLinearGroup.scalar (Fin 4) u := by
  rw [Matrix.GeneralLinearGroup.scalar_commute, ← mul_assoc, inv_mul_cancel, one_mul]

theorem ιF_comm_yP {x : E} (hx : validE x = true) :
    yP (ModelData.lin F) * ιF F x = ιF F x * yP (ModelData.lin F) := by
  rw [ιF_eq hx]
  change mkP (ModelData.lin F) (ModelData.lin F).yK * _ = _ * mkP (ModelData.lin F) (ModelData.lin F).yK
  rw [← map_mul, ← map_mul, mkP_eq_iff]
  obtain ⟨ε, hε⟩ := glE_comm_y (F := F) hx
  refine ⟨ε, ?_⟩
  show (yGL F * glE x)⁻¹ * (glE x * yGL F) = _
  rw [hε]
  exact inv_mul_scalar_mul ε _

theorem mkM_four : (mkM 4 0 0 4 : Matrix (Fin 2) (Fin 2) F) = -1 := by
  have h4 : cF F (4 : Fin 5) = -1 := by
    rw [show (4 : Fin 5) = -1 from by decide, cF_neg, cF_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mkM, h4, cF_zero]

theorem normE_zE : normE zE = zE := by rfl

theorem mat4_zE : (mat4 zE : Matrix (Fin 4) (Fin 4) F) = blk4 1 (-1) := by
  simp [mat4, zE, blkA, blkB, mkM_one, mkM_four]

theorem ιF_zE : ιF F zE = yP (ModelData.lin F) := by
  have hA : detA zE ≠ 0 := by decide
  have hP : detA zE * detB zE = 1 := by decide
  have h := ιF_normE_eq (F := F) hA hP ((ModelData.lin F).xyGL_mem_K4) (by rw [xyGL_mat, mat4_zE])
  rw [normE_zE] at h
  rw [h]
  change mkP (ModelData.lin F) (ModelData.lin F).xyK = mkP (ModelData.lin F) (ModelData.lin F).yK
  have h1 : mkP (ModelData.lin F) (ModelData.lin F).xK = 1 :=
    (QuotientGroup.eq_one_iff _).2 (xK_mem_Zs (ModelData.lin F))
  rw [← (ModelData.lin F).xK_mul_yK, map_mul, h1, one_mul]

theorem two_ne_zero_F : (2 : F) ≠ 0 := by
  intro h
  have : ((2 : ℕ) : F) = 0 := by exact_mod_cast h
  rw [CharP.cast_eq_zero_iff F 5] at this
  omega

theorem exists_rec [Finite F] (hF : Nat.card F = 5) (P Q : Matrix (Fin 2) (Fin 2) F)
    (hdet : P.det * Q.det = 1) (s : Bool) :
    ∃ z : E, detA z ≠ 0 ∧ detA z * detB z = 1 ∧ (blkA z : Matrix (Fin 2) (Fin 2) F) = P ∧
      (blkB z : Matrix (Fin 2) (Fin 2) F) = Q ∧ z.s = s := by
  obtain ⟨p0, p1, p2, p3, hp⟩ := exists_mkM hF P
  obtain ⟨q0, q1, q2, q3, hq⟩ := exists_mkM hF Q
  have hdA : cF F (p0 * p3 - p1 * p2) = P.det := by rw [hp, det_mkM]
  have hdB : cF F (q0 * q3 - q1 * q2) = Q.det := by rw [hq, det_mkM]
  refine ⟨⟨p0, p1, p2, p3, q0, q1, q2, q3, s⟩, ?_, ?_, hp.symm, hq.symm, rfl⟩
  · intro h0
    have h0' : P.det = 0 := by rw [← hdA]; exact (cF_eq_zero (F := F)).2 h0
    rw [h0', zero_mul] at hdet
    exact zero_ne_one hdet
  · apply cF_injective (F := F)
    show cF F ((p0 * p3 - p1 * p2) * (q0 * q3 - q1 * q2)) = cF F 1
    rw [cF_mul, hdA, hdB, hdet, cF_one]

theorem S_Cs [Finite F] (hF : Nat.card F = 5) :
    ((Subgroup.centralizer ({yP (ModelData.lin F)} : Set (PG (ModelData.lin F))) :
      Subgroup (PG (ModelData.lin F))) : Set (PG (ModelData.lin F))) = S (ιF F) Cs := by
  ext g
  rw [mem_S]
  constructor
  · intro hg
    have hg' : g ∈ Subgroup.centralizer ({yP (ModelData.lin F)} : Set (PG (ModelData.lin F))) := hg
    rw [centralizer_yP] at hg'
    obtain ⟨h, hh, rfl⟩ := hg'
    rcases (mem_Nsub_iff_D (ModelData.lin F)).1 hh with hD | hD
    · have hc : (h : GL (Fin 4) F) * yGL F = yGL F * (h : GL (Fin 4) F) :=
        congrArg Subtype.val (mem_Dsub.1 hD)
      obtain ⟨a, b, hab, -, -, hdet⟩ :=
        (ModelData.lin F).exists_diagGL_of_comm two_ne_zero_F h.2 hc
      obtain ⟨z, hA, hP, hzA, hzB, hzs⟩ :=
        exists_rec hF (a : Matrix (Fin 2) (Fin 2) F) (b : Matrix (Fin 2) (Fin 2) F) hdet false
      refine ⟨normE z, (mem_Cs_iff _).2 (validE_normE hA hP), ?_⟩
      have hm : ((h : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = mat4 z := by
        rw [hab, coe_diagGL, mat4, hzA, hzB, hzs]
        simp
      rw [ιF_normE_eq hA hP h.2 hm]
    · have hc : (((ModelData.lin F).wK * h : ↥(ModelData.lin F).K4) : GL (Fin 4) F) * yGL F =
          yGL F * (((ModelData.lin F).wK * h : ↥(ModelData.lin F).K4) : GL (Fin 4) F) :=
        congrArg Subtype.val (mem_Dsub.1 hD)
      obtain ⟨a, b, hab, -, -, hdet⟩ :=
        (ModelData.lin F).exists_diagGL_of_comm two_ne_zero_F ((ModelData.lin F).wK * h).2 hc
      have hh1 : (h : GL (Fin 4) F) = swapGL F * diagGL a b := by
        have : swapGL F * (h : GL (Fin 4) F) = diagGL a b := hab
        rw [← this, ← mul_assoc, swapGL_mul_self, one_mul]
      obtain ⟨z, hA, hP, hzA, hzB, hzs⟩ :=
        exists_rec hF (b : Matrix (Fin 2) (Fin 2) F) (a : Matrix (Fin 2) (Fin 2) F)
          (by rw [mul_comm]; exact hdet) true
      refine ⟨normE z, (mem_Cs_iff _).2 (validE_normE hA hP), ?_⟩
      have hm : ((h : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = mat4 z := by
        rw [hh1, Units.val_mul, coe_swapGL, coe_diagGL, wMat_mul_blk4, mat4, hzA, hzB, hzs]
        simp
      rw [ιF_normE_eq hA hP h.2 hm]
  · rintro ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact ιF_comm_yP ((mem_Cs_iff x).1 hx)

end CFSG.GH74.GLS.LU.Local.FiveStd.Mat
