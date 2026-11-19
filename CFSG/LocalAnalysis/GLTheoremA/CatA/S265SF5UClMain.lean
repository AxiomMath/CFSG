module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SF5UResDef
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SF5UClFront
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SF5UClLin
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SF5UClOm
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SF5UClSp
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SF5UClUni

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265.SF5U

open CFSG.Blueprint (LieModel)
open CFSG.Blueprint.LieModel (statedClassicalModel)


theorem qsF5UCls_holds : QSF5UCls := by
  rintro Ω _ _ S B T x D K h hK hZK h25 ⟨t, r, k⟩ hlab _ _ htag
  dsimp only at htag
  have hnd : t ≠ .B2der ∧ t ≠ .G2der ∧ t ≠ .twF4der := by
    rcases htag with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  obtain ⟨G, _, _, β, J, e, hG, hβ, hβ5, hβ1, hJ, hZ, hJc, h5, h25'⟩ :=
    exists_cls_data_of_qsnl h hK hZK h25 hlab hnd
  have he : 1 ≤ e := by
    rcases Nat.eq_zero_or_pos e with rfl | he
    · norm_num at h5
    · exact he
  rcases htag with rfl | rfl | rfl | rfl | rfl | rfl
  · exact false_of_classicalModel_psl (statedClassicalModel hG (by decide)) hβ hβ5 hJ hZ he hJc
  · exact false_of_classicalModel_psu (statedClassicalModel hG (by decide)) hβ hβ5 hβ1 hJ hZ h5
      h25' hJc
  · exact false_of_classicalModel_psp (statedClassicalModel hG (by decide)) hβ hβ5 hβ1 hJ hZ h5
      hJc
  · exact false_of_classicalModel_psp (statedClassicalModel hG (by decide)) hβ hβ5 hβ1 hJ hZ h5
      hJc
  · have hG' : LieModel G (if r = 3 then .PSL else .POmegaPlus) (if r = 3 then 4 else r) 2 k :=
      hG
    by_cases hr : r = 3
    · rw [ite_eq_left hr, ite_eq_left hr] at hG'
      exact false_of_classicalModel_psl (statedClassicalModel hG' (by decide)) hβ hβ5 hJ hZ he hJc
    · rw [ite_eq_right hr, ite_eq_right hr] at hG'
      exact false_of_classicalModel_pomega (Or.inl rfl) (statedClassicalModel hG' (by decide)) hβ
        hβ5 hJ hZ h5 hJc
  · have hG' : LieModel G (if r = 2 then .PSL else if r = 3 then .PSU else .POmegaMinus)
        (if r = 2 then 2 else if r = 3 then 4 else r) 2 (if r = 2 then 2 * k else k) := hG
    by_cases hr2 : r = 2
    · rw [ite_eq_left hr2, ite_eq_left hr2, ite_eq_left hr2] at hG'
      exact false_of_classicalModel_psl (statedClassicalModel hG' (by decide)) hβ hβ5 hJ hZ he hJc
    by_cases hr3 : r = 3
    · rw [ite_eq_right hr2, ite_eq_right hr2, ite_eq_right hr2, ite_eq_left hr3, ite_eq_left hr3] at hG'
      exact false_of_classicalModel_psu (statedClassicalModel hG' (by decide)) hβ hβ5 hβ1 hJ hZ h5
        h25' hJc
    · rw [ite_eq_right hr2, ite_eq_right hr2, ite_eq_right hr2, ite_eq_right hr3, ite_eq_right hr3] at hG'
      exact false_of_classicalModel_pomega (Or.inr rfl) (statedClassicalModel hG' (by decide)) hβ
        hβ5 hJ hZ h5 hJc

end CFSG.LocalAnalysis.GLTheoremA.S265.SF5U

end
