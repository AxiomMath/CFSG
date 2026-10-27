module

public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourAutomorphisms
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherLinearPureGraph
import all CFSG.LocalAnalysis.ComponentClassification.PSL3FourActionData

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.Hin.SporX

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.ComponentClassification.PSL3Four

@[expose] def onMat5 : Matrix (Fin 3) (Fin 3) F4 := !![0, 0, 1; ⟨2⟩, ⟨3⟩, 0; ⟨3⟩, ⟨2⟩, 0]

@[expose] def onMat7 : Matrix (Fin 3) (Fin 3) F4 := !![0, 0, 1; 1, 0, 1; 0, 1, 0]

@[expose] def onSL5 : SpecialLinearGroup (Fin 3) F4 :=
  ⟨onMat5, by rw [det_fin_three]; decide⟩

@[expose] def onSL7 : SpecialLinearGroup (Fin 3) F4 :=
  ⟨onMat7, by rw [det_fin_three]; decide⟩

theorem not_mem_scalars_of_entry {g : SpecialLinearGroup (Fin 3) F4}
    (h : (g : Matrix (Fin 3) (Fin 3) F4) 0 2 = 1) : g ∉ scalars 3 F4 := by
  rintro ⟨c, -, hc⟩
  have h1 := congrFun (congrFun hc 0) 2
  rw [h, scalar_apply, diagonal_apply_ne _ (by decide)] at h1
  exact one_ne_zero h1

theorem onSL5_mul_transpose : onSL5 * onSL5.transpose = 1 := by
  have h : (onMat5 * onMat5ᵀ : Matrix (Fin 3) (Fin 3) F4) = 1 := by decide
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_transpose,
    Matrix.SpecialLinearGroup.coe_one]
  exact congrFun (congrFun h i) j

theorem dualAut_proj_onSL5 : dualAut 3 F4 (proj 3 F4 onSL5) = proj 3 F4 onSL5 := by
  have h : (onSL5⁻¹).transpose = onSL5 := by
    rw [← eq_inv_of_mul_eq_one_right onSL5_mul_transpose]
    exact Matrix.SpecialLinearGroup.ext _ _ fun i j => by
      rw [Matrix.SpecialLinearGroup.coe_transpose, Matrix.SpecialLinearGroup.coe_transpose,
        transpose_transpose]
  rw [dualAut_proj, h]

theorem fieldAut_proj_onSL7 : fieldAut 3 F4 frob (proj 3 F4 onSL7) = proj 3 F4 onSL7 := by
  have h : onMat7.map frob = onMat7 := by decide
  have h1 : SpecialLinearGroup.map frob.toRingHom onSL7 = onSL7 :=
    Matrix.SpecialLinearGroup.ext _ _ fun i j => by
      rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
      exact congrFun (congrFun h i) j
  rw [fieldAut_proj, h1]

theorem orderOf_proj_onSL5 : orderOf (proj 3 F4 onSL5) = 5 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  refine orderOf_eq_prime ?_ ?_
  · have h0 : (onMat5 ^ 5 : Matrix (Fin 3) (Fin 3) F4) = 1 := by decide
    have h : onSL5 ^ 5 = 1 := Matrix.SpecialLinearGroup.ext _ _ fun i j => by
      rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
      exact congrFun (congrFun h0 i) j
    rw [← map_pow, h, map_one]
  · rw [Ne, proj_eq_one_iff]
    exact not_mem_scalars_of_entry rfl

theorem orderOf_proj_onSL7 : orderOf (proj 3 F4 onSL7) = 7 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  refine orderOf_eq_prime ?_ ?_
  · have h0 : (onMat7 ^ 7 : Matrix (Fin 3) (Fin 3) F4) = 1 := by decide
    have h : onSL7 ^ 7 = 1 := Matrix.SpecialLinearGroup.ext _ _ fun i j => by
      rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
      exact congrFun (congrFun h0 i) j
    rw [← map_pow, h, map_one]
  · rw [Ne, proj_eq_one_iff]
    exact not_mem_scalars_of_entry rfl

theorem natCard_F4 : Nat.card F4 = 2 ^ 2 := by
  rw [Nat.card_eq_fintype_card, F4.card_eq]
  norm_num

theorem frob_ne_one : frob ≠ 1 := by
  intro h
  have h1 : frob F4.ω = F4.ω := by rw [h]; rfl
  rw [frob_apply] at h1
  exact absurd h1 (by decide)

theorem conj_fixed {G : Type*} [Group G] (h β : MulAut G) {s : G} (hs : β s = s) :
    (h * β * h⁻¹) (h s) = h s := by
  rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self, hs]

theorem exists_fixed_five_of_graph (A : GL (Fin 3) F4)
    (hα : (conjAut 3 F4 A * dualAut 3 F4) * (conjAut 3 F4 A * dualAut 3 F4) = 1) :
    ∃ s : projectiveSL 3 F4, (conjAut 3 F4 A * dualAut 3 F4) s = s ∧ orderOf s = 5 := by
  obtain ⟨-, ⟨H, C, -, hHC, hC⟩, -⟩ :=
    UnitaryHigher.even_linear_pure_graph_involution_normal_forms (by norm_num) natCard_F4
      (le_refl 3) A (by rw [pow_two]; exact hα)
  have hC1 : C = 1 := by
    rcases hC with ⟨hC, -⟩ | ⟨r, hr, -⟩
    · exact Units.ext hC
    · omega
  rw [hHC, hC1, map_one, one_mul]
  refine ⟨conjAut 3 F4 H (proj 3 F4 onSL5), conj_fixed _ _ dualAut_proj_onSL5, ?_⟩
  rw [MulEquiv.orderOf_eq]
  exact orderOf_proj_onSL5

theorem exists_fixed_seven_of_field (A : GL (Fin 3) F4)
    (hα : (conjAut 3 F4 A * fieldAut 3 F4 frob) * (conjAut 3 F4 A * fieldAut 3 F4 frob) = 1) :
    ∃ s : projectiveSL 3 F4, (conjAut 3 F4 A * fieldAut 3 F4 frob) s = s ∧ orderOf s = 7 := by
  obtain ⟨-, -, H, hH⟩ := even_linear_field_involution_descent (by norm_num) natCard_F4
    (le_refl 3) A frob frob_ne_one (by rw [pow_two]; exact hα)
  rw [hH]
  refine ⟨conjAut 3 F4 H (proj 3 F4 onSL7), conj_fixed _ _ fieldAut_proj_onSL7, ?_⟩
  rw [MulEquiv.orderOf_eq]
  exact orderOf_proj_onSL7

end CFSG.ComponentClassification.HarrisLit.Hin.SporX
