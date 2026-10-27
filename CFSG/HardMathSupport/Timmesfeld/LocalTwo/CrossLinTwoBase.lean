module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ProjectiveSemilinear
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.HardMathSupport.Foote.ModuleExclusions.Hilbert90

public section

namespace CFSG.HardMathSupport.Timmesfeld.LocalTwo

open CFSG CFSG.GorensteinWalter

section Field

variable {F : Type} [Field F] [Finite F]

theorem ringEquiv_mem_zpowers_of_fixes (σ τ : F ≃+* F) (h : ∀ a : F, σ a = a → τ a = a) :
    τ ∈ Subgroup.zpowers σ := by
  classical
  let G := Subgroup.zpowers σ
  have hfix : ∀ r : FixedPoints.subfield G F, τ (r : F) = r := fun r =>
    h r (by
      have := r.2 ⟨σ, Subgroup.mem_zpowers σ⟩
      exact this)
  let τ' : F →ₐ[FixedPoints.subfield G F] F :=
    { τ.toRingHom with commutes' := fun r => hfix r }
  obtain ⟨g, hg⟩ := (FixedPoints.toAlgHom_bijective G F).2 τ'
  have : τ = (g : F ≃+* F) := by
    ext x
    have := DFunLike.congr_fun hg x
    exact this.symm
  rw [this]
  exact g.2

end Field

section Transvection

variable {F : Type} [Field F]

@[expose] def tvPSL (i j : Fin 2) (hij : i ≠ j) (a : F) : PSL2 F :=
  QuotientGroup.mk' (Subgroup.center _) (Matrix.SpecialLinearGroup.transvection hij a)

theorem psl2FieldAut_tvPSL (σ : F ≃+* F) (i j : Fin 2) (hij : i ≠ j) (a : F) :
    psl2FieldAut F σ (tvPSL i j hij a) = tvPSL i j hij (σ a) := by
  classical
  rw [psl2FieldAut_apply]
  unfold tvPSL
  rw [psl2RingEquiv_mk]
  congr 1
  ext x y
  by_cases h : i = x ∧ j = y <;>
    simp [Matrix.SpecialLinearGroup.transvection_coe, Matrix.one_apply, h]

theorem tvPSL_injective (i j : Fin 2) (hij : i ≠ j) : Function.Injective (tvPSL (F := F) i j hij) := by
  intro a b hab
  have hq : (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F))
      (Matrix.SpecialLinearGroup.transvection hij a)) =
      QuotientGroup.mk' (Subgroup.center _) (Matrix.SpecialLinearGroup.transvection hij b) := hab
  have hcent := QuotientGroup.eq_iff_div_mem.mp hq
  have hdiff : Matrix.SpecialLinearGroup.transvection hij a /
      Matrix.SpecialLinearGroup.transvection hij b =
        Matrix.SpecialLinearGroup.transvection hij (a - b) := by
    rw [div_eq_mul_inv, Matrix.SpecialLinearGroup.transvection_inv,
      ← Matrix.SpecialLinearGroup.transvection_add, sub_eq_add_neg]
  rw [hdiff, Matrix.SpecialLinearGroup.transvection_mem_center_iff] at hcent
  exact sub_eq_zero.mp hcent

theorem pgl2_eq_one_of_commute_unit_tv (g : PGL2 F)
    (hU : Commute g (Matrix.ProjectiveSpecialLinearGroup.toPGL (tvPSL 0 1 (by decide) (1 : F))))
    (hL : Commute g (Matrix.ProjectiveSpecialLinearGroup.toPGL (tvPSL 1 0 (by decide) (1 : F)))) :
    g = 1 := by
  induction g using Matrix.ProjGenLinGroup.induction_on with
  | mk A =>
      rw [Matrix.ProjGenLinGroup.mk_eq_one]
      rw [Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar]
      let U : Matrix.SpecialLinearGroup (Fin 2) F :=
        Matrix.SpecialLinearGroup.transvection
          (show (0 : Fin 2) ≠ 1 by decide) 1
      let L : Matrix.SpecialLinearGroup (Fin 2) F :=
        Matrix.SpecialLinearGroup.transvection
          (show (1 : Fin 2) ≠ 0 by decide) 1
      have hUq :
          Matrix.ProjGenLinGroup.mk
              (A * Matrix.SpecialLinearGroup.toGL U) =
            Matrix.ProjGenLinGroup.mk
              (Matrix.SpecialLinearGroup.toGL U * A) := by
        rw [map_mul, map_mul]
        simpa [tvPSL, U] using hU.eq
      have hLq :
          Matrix.ProjGenLinGroup.mk
              (A * Matrix.SpecialLinearGroup.toGL L) =
            Matrix.ProjGenLinGroup.mk
              (Matrix.SpecialLinearGroup.toGL L * A) := by
        rw [map_mul, map_mul]
        simpa [tvPSL, L] using hL.eq
      rcases Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp hUq with ⟨r, hr⟩
      rcases Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp hLq with ⟨s, hs⟩
      have hU10 := congrArg (fun B : GL (Fin 2) F ↦
        ((B : Matrix (Fin 2) (Fin 2) F) 1 0)) hr
      have hU11 := congrArg (fun B : GL (Fin 2) F ↦
        ((B : Matrix (Fin 2) (Fin 2) F) 1 1)) hr
      have hr1 : (r : F) = 1 := by
        by_contra hrne
        have hc : (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
          by_contra hcne
          apply hrne
          apply mul_left_cancel₀ hcne
          simpa [U, Matrix.GeneralLinearGroup.scalar,
            Matrix.SpecialLinearGroup.transvection_coe,
            Matrix.mul_apply, Fin.sum_univ_two] using hU10
        have hd : (A : Matrix (Fin 2) (Fin 2) F) 1 1 = 0 := by
          by_contra hdne
          apply hrne
          apply mul_left_cancel₀ hdne
          simpa [U, hc, Matrix.GeneralLinearGroup.scalar,
            Matrix.SpecialLinearGroup.transvection_coe,
            Matrix.mul_apply, Fin.sum_univ_two] using hU11
        apply A.det_ne_zero
        apply Matrix.det_eq_zero_of_row_eq_zero 1
        intro j
        fin_cases j <;> assumption
      have hU00 := congrArg (fun B : GL (Fin 2) F ↦
        ((B : Matrix (Fin 2) (Fin 2) F) 0 0)) hr
      have hU01 := congrArg (fun B : GL (Fin 2) F ↦
        ((B : Matrix (Fin 2) (Fin 2) F) 0 1)) hr
      have hc : (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
        simpa [U, hr1, Matrix.GeneralLinearGroup.scalar,
          Matrix.SpecialLinearGroup.transvection_coe,
          Matrix.mul_apply, Fin.sum_univ_two] using hU00
      have had : (A : Matrix (Fin 2) (Fin 2) F) 0 0 =
          (A : Matrix (Fin 2) (Fin 2) F) 1 1 := by
        have h := hU01
        simp [U, hr1, Matrix.GeneralLinearGroup.scalar,
          Matrix.SpecialLinearGroup.transvection_coe,
          Matrix.mul_apply, Fin.sum_univ_two] at h
        apply add_right_cancel
          (b := (A : Matrix (Fin 2) (Fin 2) F) 0 1)
        simpa [add_comm] using h
      have hL00 := congrArg (fun B : GL (Fin 2) F ↦
        ((B : Matrix (Fin 2) (Fin 2) F) 0 0)) hs
      have hL01 := congrArg (fun B : GL (Fin 2) F ↦
        ((B : Matrix (Fin 2) (Fin 2) F) 0 1)) hs
      have hs1 : (s : F) = 1 := by
        by_contra hsne
        have hb : (A : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 := by
          by_contra hbne
          apply hsne
          apply mul_left_cancel₀ hbne
          simpa [L, Matrix.GeneralLinearGroup.scalar,
            Matrix.SpecialLinearGroup.transvection_coe,
            Matrix.mul_apply, Fin.sum_univ_two] using hL01
        have ha : (A : Matrix (Fin 2) (Fin 2) F) 0 0 = 0 := by
          by_contra hane
          apply hsne
          apply mul_left_cancel₀ hane
          simpa [L, hb, Matrix.GeneralLinearGroup.scalar,
            Matrix.SpecialLinearGroup.transvection_coe,
            Matrix.mul_apply, Fin.sum_univ_two] using hL00
        apply A.det_ne_zero
        apply Matrix.det_eq_zero_of_row_eq_zero 0
        intro j
        fin_cases j <;> assumption
      have hb : (A : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 := by
        simpa [L, hs1, Matrix.GeneralLinearGroup.scalar,
          Matrix.SpecialLinearGroup.transvection_coe,
          Matrix.mul_apply, Fin.sum_univ_two] using hL00
      refine ⟨(A : Matrix (Fin 2) (Fin 2) F) 0 0, ?_⟩
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.scalar_apply, hb, hc, had]

end Transvection

end CFSG.HardMathSupport.Timmesfeld.LocalTwo
