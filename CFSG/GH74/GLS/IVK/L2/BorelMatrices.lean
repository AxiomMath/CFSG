module

public import CFSG.GH74.GLS.IVK.L2.BNMatrices
public import CFSG.CharacterTheory.PSL2Table.Basic

public section

namespace CFSG.GH74.GLS.IVK.L2Borel

open CFSG.PSL2Table
open scoped MatrixGroups

variable {F : Type} [Field F]

@[expose] def lowT (s : F) : SL(2, F) :=
  ⟨!![1, 0; s, 1], by simp [Matrix.det_fin_two_of]⟩

@[expose] def wc (c : F) (hc : c ≠ 0) : SL(2, F) :=
  ⟨!![0, -c⁻¹; c, 0], by simp [Matrix.det_fin_two_of, hc]⟩

@[simp] theorem coe_lowT (s : F) :
    (lowT s : Matrix (Fin 2) (Fin 2) F) = !![1, 0; s, 1] := rfl

@[simp] theorem coe_wc (c : F) (hc : c ≠ 0) :
    (wc c hc : Matrix (Fin 2) (Fin 2) F) = !![0, -c⁻¹; c, 0] := rfl

theorem transvection_zero_one (t : F) :
    Matrix.SpecialLinearGroup.transvection (zero_ne_one : (0 : Fin 2) ≠ 1) t = unip t := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.transvection_coe]

theorem transvection_one_zero (t : F) :
    Matrix.SpecialLinearGroup.transvection (one_ne_zero : (1 : Fin 2) ≠ 0) t = lowT t := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.transvection_coe]

theorem unip_mul_mul_unip (A : SL(2, F)) (hc : (A : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0) :
    unip (-((A : Matrix (Fin 2) (Fin 2) F) 0 0 / (A : Matrix (Fin 2) (Fin 2) F) 1 0)) * A *
      unip (-((A : Matrix (Fin 2) (Fin 2) F) 1 1 / (A : Matrix (Fin 2) (Fin 2) F) 1 0)) =
        wc ((A : Matrix (Fin 2) (Fin 2) F) 1 0) hc := by
  have hdet := det_entries A
  apply SL_ext <;> simp [mul_apply_SL] <;> field_simp <;>
    first | ring1 | linear_combination (-1 : F) * hdet

theorem wc_conj_unip (c : F) (hc : c ≠ 0) (t : F) :
    wc c hc * unip t * (wc c hc)⁻¹ = lowT (-(c ^ 2 * t)) := by
  apply SL_ext <;> simp [mul_apply_SL, Matrix.adjugate_fin_two] <;> field_simp

theorem eq_top_of_unip_mem {C : Subgroup SL(2, F)} (hup : ∀ t : F, unip t ∈ C) {A : SL(2, F)}
    (hA : A ∈ C) (hc : (A : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0) : C = ⊤ := by
  have hm : wc ((A : Matrix (Fin 2) (Fin 2) F) 1 0) hc ∈ C := by
    rw [← unip_mul_mul_unip A hc]
    exact C.mul_mem (C.mul_mem (hup _) hA) (hup _)
  have hlow : ∀ s : F, lowT s ∈ C := by
    intro s
    set c := (A : Matrix (Fin 2) (Fin 2) F) 1 0 with hcdef
    have h := C.mul_mem (C.mul_mem hm (hup (-(s / c ^ 2)))) (C.inv_mem hm)
    rw [wc_conj_unip] at h
    have e : -(c ^ 2 * -(s / c ^ 2)) = s := by field_simp
    rwa [e] at h
  refine eq_top_iff.2 fun B _ => ?_
  refine Matrix.SL2.transvection_induction (fun g => g ∈ C) ?_ (fun _ _ => C.mul_mem) B
  intro i j h c
  fin_cases i
  · obtain rfl : j = 1 := by fin_cases j <;> tauto
    exact (transvection_zero_one c).symm ▸ hup c
  · obtain rfl : j = 0 := by fin_cases j <;> tauto
    exact (transvection_one_zero c).symm ▸ hlow c

theorem closure_unipotent_insert_eq_top {x : PSL(2, F)} (hx : x ∉ borel F) :
    Subgroup.closure ((unipotent F : Set PSL(2, F)) ∪ {x}) = ⊤ := by
  obtain ⟨A, rfl⟩ := mk_surjective x
  have hc : (A : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0 := by
    intro h
    apply hx
    rw [mk_mem_borel_iff, mem_borelSL_iff]
    exact h
  set H := Subgroup.closure ((unipotent F : Set PSL(2, F)) ∪ {mk A}) with hH
  have hC : H.comap mk = ⊤ := by
    refine eq_top_of_unip_mem (fun t => ?_) (A := A) ?_ hc
    · exact Subgroup.subset_closure (Or.inl (mk_unip_mem_unipotent t))
    · exact Subgroup.subset_closure (Or.inr rfl)
  refine eq_top_iff.2 fun y _ => ?_
  obtain ⟨B, rfl⟩ := mk_surjective y
  have : B ∈ H.comap mk := by rw [hC]; trivial
  exact this

theorem toPGL_mk_eq (A : SL(2, F)) :
    Matrix.ProjectiveSpecialLinearGroup.toPGL (mk A) =
      Matrix.ProjGenLinGroup.mk (Matrix.SpecialLinearGroup.toGL A) := rfl

theorem exists_eq_toPGL_of_commute {t : F} (ht : t ≠ 0) {g : PGL(2, F)}
    (hg : g * Matrix.ProjectiveSpecialLinearGroup.toPGL (mk (unip t)) =
      Matrix.ProjectiveSpecialLinearGroup.toPGL (mk (unip t)) * g) :
    ∃ s : F, g = Matrix.ProjectiveSpecialLinearGroup.toPGL (mk (unip s)) := by
  induction g using Matrix.ProjGenLinGroup.induction_on with
  | mk ĝ =>
  rw [toPGL_mk_eq, ← map_mul, ← map_mul, Matrix.ProjGenLinGroup.mk_eq_mk_iff] at hg
  obtain ⟨u, hu⟩ := hg
  have e00 := congrArg (fun X : GL (Fin 2) F => (X : Matrix (Fin 2) (Fin 2) F) 0 0) hu
  have e01 := congrArg (fun X : GL (Fin 2) F => (X : Matrix (Fin 2) (Fin 2) F) 0 1) hu
  have e10 := congrArg (fun X : GL (Fin 2) F => (X : Matrix (Fin 2) (Fin 2) F) 1 0) hu
  have e11 := congrArg (fun X : GL (Fin 2) F => (X : Matrix (Fin 2) (Fin 2) F) 1 1) hu
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
  have hdet := L2BN.det_ne_zero ĝ
  have hu1 : (u : F) = 1 := by
    by_contra hne
    have hne' : (u : F) - 1 ≠ 0 := sub_ne_zero.2 hne
    have hc : (ĝ : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
      have : (ĝ : Matrix (Fin 2) (Fin 2) F) 1 0 * ((u : F) - 1) = 0 := by linear_combination e10
      exact (mul_eq_zero.1 this).resolve_right hne'
    have ha : (ĝ : Matrix (Fin 2) (Fin 2) F) 0 0 = 0 := by
      have : (ĝ : Matrix (Fin 2) (Fin 2) F) 0 0 * ((u : F) - 1) = 0 := by
        linear_combination e00 + t * hc
      exact (mul_eq_zero.1 this).resolve_right hne'
    have hd : (ĝ : Matrix (Fin 2) (Fin 2) F) 1 1 = 0 := by
      have : (ĝ : Matrix (Fin 2) (Fin 2) F) 1 1 * ((u : F) - 1) = 0 := by
        linear_combination e11 - t * (u : F) * hc
      exact (mul_eq_zero.1 this).resolve_right hne'
    apply hdet
    rw [ha, hd, hc]
    ring
  rw [hu1] at e00 e01
  have hc : (ĝ : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
    have : t * (ĝ : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by linear_combination -e00
    exact (mul_eq_zero.1 this).resolve_left ht
  have had : (ĝ : Matrix (Fin 2) (Fin 2) F) 1 1 = (ĝ : Matrix (Fin 2) (Fin 2) F) 0 0 := by
    have : t * ((ĝ : Matrix (Fin 2) (Fin 2) F) 0 0 - (ĝ : Matrix (Fin 2) (Fin 2) F) 1 1) = 0 := by
      linear_combination e01
    have := (mul_eq_zero.1 this).resolve_left ht
    linear_combination -this
  have ha0 : (ĝ : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 := by
    intro h
    apply hdet
    rw [hc, had, h]
    ring
  refine ⟨(ĝ : Matrix (Fin 2) (Fin 2) F) 0 1 / (ĝ : Matrix (Fin 2) (Fin 2) F) 0 0, ?_⟩
  rw [toPGL_mk_eq, Matrix.ProjGenLinGroup.mk_eq_mk_iff]
  refine ⟨Units.mk0 _ (inv_ne_zero ha0), ?_⟩
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hc, had] <;>
    try field_simp

end CFSG.GH74.GLS.IVK.L2Borel
