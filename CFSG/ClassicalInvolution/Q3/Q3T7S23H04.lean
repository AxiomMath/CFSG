module

public import CFSG.ClassicalInvolution.Asc77.AscT7L18
public import CFSG.ClassicalInvolution.Asc77.AscT7L21
public import CFSG.ClassicalInvolution.Q3.Q3WALoc

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T7S23

open Matrix CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.ModelFacts.Orth15.InnerL4
  CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterL4 CFSG.LieType.Universal.SpecialLinear
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Asc77
open scoped MatrixGroups

section Gen

variable {F : Type} [Field F]

theorem Xel_tr13 (β : F) :
    T7L.Xel β * T7L.tr4 (show (1 : Fin 4) ≠ 3 by decide) β =
      T7L.tr4 (show (2 : Fin 4) ≠ 3 by decide) 1 * T7L.Xel β *
        T7L.tr4 (show (2 : Fin 4) ≠ 3 by decide) (-1) := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, T7L.coe_Xel, SpecialLinearGroup.transvection_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.single_apply, Matrix.one_apply]

theorem Yel_tr31 (β : F) :
    T7L.Yel β * T7L.tr4 (show (3 : Fin 4) ≠ 1 by decide) β =
      T7L.tr4 (show (3 : Fin 4) ≠ 2 by decide) 1 * T7L.Yel β *
        T7L.tr4 (show (3 : Fin 4) ≠ 2 by decide) (-1) := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, T7L.coe_Yel, SpecialLinearGroup.transvection_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.single_apply, Matrix.one_apply]

theorem tr12_eq_comm (β : F) :
    T7L.tr4 (show (1 : Fin 4) ≠ 2 by decide) β =
      T7L.tr4 (show (1 : Fin 4) ≠ 3 by decide) β * T7L.tr4 (show (3 : Fin 4) ≠ 2 by decide) 1 *
        T7L.tr4 (show (1 : Fin 4) ≠ 3 by decide) (-β) *
          T7L.tr4 (show (3 : Fin 4) ≠ 2 by decide) (-1) := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, SpecialLinearGroup.transvection_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.single_apply, Matrix.one_apply]

theorem tr21_eq_comm (β : F) :
    T7L.tr4 (show (2 : Fin 4) ≠ 1 by decide) β =
      T7L.tr4 (show (2 : Fin 4) ≠ 3 by decide) 1 * T7L.tr4 (show (3 : Fin 4) ≠ 1 by decide) β *
        T7L.tr4 (show (2 : Fin 4) ≠ 3 by decide) (-1) *
          T7L.tr4 (show (3 : Fin 4) ≠ 1 by decide) (-β) := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, SpecialLinearGroup.transvection_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.single_apply, Matrix.one_apply]

theorem top_le_centralizer_x0_sup_u0_gen :
    (⊤ : Subgroup SL(4, F)) ≤ Subgroup.centralizer ({x0 F} : Set SL(4, F)) ⊔
      Subgroup.centralizer ({u0 F} : Set SL(4, F)) := by
  set H : Subgroup SL(4, F) := Subgroup.centralizer ({x0 F} : Set SL(4, F)) ⊔
    Subgroup.centralizer ({u0 F} : Set SL(4, F)) with hH
  have hx : ∀ g : SL(4, F), g * x0 F = x0 F * g → g ∈ H := fun g hg =>
    Subgroup.mem_sup_left (Subgroup.mem_centralizer_singleton_iff.mpr hg)
  have hu : ∀ g : SL(4, F), g * u0 F = u0 F * g → g ∈ H := fun g hg =>
    Subgroup.mem_sup_right (Subgroup.mem_centralizer_singleton_iff.mpr hg)
  have g23 : ∀ c : F, T7L.tr4 (show (2 : Fin 4) ≠ 3 by decide) c ∈ H := fun c =>
    hx _ (T7L.tr4_comm_x0_23 c)
  have g32 : ∀ c : F, T7L.tr4 (show (3 : Fin 4) ≠ 2 by decide) c ∈ H := fun c =>
    hx _ (T7L.tr4_comm_x0_32 c)
  have h13 : ∀ β : F, T7L.tr4 (show (1 : Fin 4) ≠ 3 by decide) β ∈ H := by
    intro β
    have hX : T7L.Xel β ∈ H := hu _ (T7L.Xel_comm_u0 β)
    have e : T7L.tr4 (show (1 : Fin 4) ≠ 3 by decide) β = (T7L.Xel β)⁻¹ *
        (T7L.tr4 (show (2 : Fin 4) ≠ 3 by decide) 1 * T7L.Xel β *
          T7L.tr4 (show (2 : Fin 4) ≠ 3 by decide) (-1)) := by
      rw [← Xel_tr13 β]
      group
    rw [e]
    exact H.mul_mem (H.inv_mem hX) (H.mul_mem (H.mul_mem (g23 1) hX) (g23 (-1)))
  have h31 : ∀ β : F, T7L.tr4 (show (3 : Fin 4) ≠ 1 by decide) β ∈ H := by
    intro β
    have hY : T7L.Yel β ∈ H := hu _ (T7L.Yel_comm_u0 β)
    have e : T7L.tr4 (show (3 : Fin 4) ≠ 1 by decide) β = (T7L.Yel β)⁻¹ *
        (T7L.tr4 (show (3 : Fin 4) ≠ 2 by decide) 1 * T7L.Yel β *
          T7L.tr4 (show (3 : Fin 4) ≠ 2 by decide) (-1)) := by
      rw [← Yel_tr31 β]
      group
    rw [e]
    exact H.mul_mem (H.inv_mem hY) (H.mul_mem (H.mul_mem (g32 1) hY) (g32 (-1)))
  have h12 : ∀ c : F, T7L.tr4 (show (1 : Fin 4) ≠ 2 by decide) c ∈ H := by
    intro c
    rw [tr12_eq_comm]
    exact H.mul_mem (H.mul_mem (H.mul_mem (h13 c) (g32 1)) (h13 (-c))) (g32 (-1))
  have h21 : ∀ c : F, T7L.tr4 (show (2 : Fin 4) ≠ 1 by decide) c ∈ H := by
    intro c
    rw [tr21_eq_comm]
    exact H.mul_mem (H.mul_mem (H.mul_mem (g23 1) (h31 c)) (g23 (-1))) (h31 (-c))
  have hall := T7L.fund_le_of_adjacent (H := H) (fun c => hx _ (T7L.tr4_comm_x0_01 c))
    (fun c => hx _ (T7L.tr4_comm_x0_10 c)) h12 h21 g23 g32
  rw [iSup_fundamentalRootSubgroup_eq_top (m := 3) (F := F)] at hall
  exact hall

end Gen

section Rows


theorem e4GenSp_3 (hadm : StatedLieAdmissible .PSp 2 3 1) : E4GenAt 3 .PSp 2 1 := by
  have h2 : (2 : GaloisField 3 1) ≠ 0 := Q3W.two_ne_zero_gf3
  intro R hR R' hR' hne hcomm x hx hx2 hx1 x' hx' hx'2 hx'1 hxx' a ha haa b hb hbb
  have hRl := (ModelFacts.fund_iff_isLongRootSp2 hadm h2 R).1 hR
  have hRl' := (ModelFacts.fund_iff_isLongRootSp2 hadm h2 R').1 hR'
  have hc : x' * x⁻¹ ∈ Subgroup.center (StatedSp 2 (GaloisField 3 1)) := by
    have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
    rw [hxinv, ← hcomm x hx x' hx']
    exact hxx'
  exact T7L.e4_goal_of_top_le _ _ _ (T7L.top_le_sup_sp h2 hRl hRl' hne hx hx2 hx1 hx' hx'2 hx'1 hc
    ha haa hb hbb (hcomm a ha b hb))

theorem e4GenSL_3 : E4GenAt 3 .PSL 4 1 := by
  have h2 : (2 : GaloisField 3 1) ≠ 0 := Q3W.two_ne_zero_gf3
  intro R hR R' hR' hne hcomm x hx hx2 hx1 x' hx' hx'2 hx'1 hxx' a ha haa b hb hbb
  have hRl := fundamentalSubgroups_psl_subset (m := 3) (F := GaloisField 3 1) (by norm_num) hR
  have hRl' := fundamentalSubgroups_psl_subset (m := 3) (F := GaloisField 3 1) (by norm_num) hR'
  have hc : x' * x⁻¹ ∈ Subgroup.center SL(4, GaloisField 3 1) := by
    have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
    rw [hxinv, ← hcomm x hx x' hx']
    exact hxx'
  obtain ⟨c, hxc, habc⟩ := T7L.exists_conj_x0_u0 h2 hRl hRl' hne hx hx2 hx1 hx' hx'2 hx'1 hc ha haa
    hb hbb
  exact T7L.e4_goal_of_top_le _ _ _
    (T7L.top_le_sup_of_conj c hxc habc top_le_centralizer_x0_sup_u0_gen)

end Rows

end CFSG.ClassicalInvolution.Q3.Q3T7S23
