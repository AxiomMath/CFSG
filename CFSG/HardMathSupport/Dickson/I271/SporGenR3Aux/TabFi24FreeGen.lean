module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24ThreeFix

public section

namespace CFSG.HardMathSupport.Dickson.I271.TabFi24

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Three
open CFSG.Sporadic.Fi24 (R J JR jR tR cls lvl gs letters)
open CFSG.Sporadic.FischerOddCore (cls_smul_eq_iff)

attribute [local instance] CFSG.Sporadic.Fi24.rAction

set_option linter.unusedSectionVars false

section Comm

@[expose] def Cm (a b : Fin 306936) : Prop := cls a * cls b = cls b * cls a

theorem Cm.symm {a b : Fin 306936} (h : Cm a b) : Cm b a := Eq.symm h

theorem cls_smul_self' (k : Fin 306936) : cls k • k = k :=
  (smul_eq_iff_commute_R (cls k) k).2 rfl

end Comm

section Lines

@[expose] noncomputable def third (a b : Fin 306936) : Fin 306936 := cls a • b

theorem fst_ne_snd {a b : Fin 306936} (h : ¬Cm a b) : a ≠ b := fun e => h (by subst e; rfl)

theorem third_ne_snd {a b : Fin 306936} (h : ¬Cm a b) : third a b ≠ b := fun e =>
  h ((cls_smul_eq_iff a b).1 e)

theorem third_ne_fst {a b : Fin 306936} (h : ¬Cm a b) : third a b ≠ a := by
  intro e
  have e1 : cls (third a b) = cls a * cls b * (cls a)⁻¹ :=
    CFSG.Sporadic.Fi24.cls_smul_R (cls a) b
  rw [e] at e1
  have e2 : cls a * cls a = cls a * cls b := by
    calc cls a * cls a = cls a * cls b * (cls a)⁻¹ * cls a := by rw [← e1]
      _ = cls a * cls b := by group
  exact fst_ne_snd h (CFSG.Sporadic.Fi24.cls_injective (mul_left_cancel e2))

theorem line_cube {a b : Fin 306936} (h : ¬Cm a b) {w : J} (hw : jR w = cls a * cls b) :
    w ^ 3 = 1 := by
  apply CFSG.Sporadic.Fi24.jR_injective
  rw [map_pow, hw, map_one, pow_three']
  exact cls_cube h

theorem line_smul_fst {a b : Fin 306936} (h : ¬Cm a b) {w : J} (hw : jR w = cls a * cls b) :
    w • a = b := by
  rw [← CFSG.Sporadic.Fi24.jR_smul, hw]
  exact cls_mul_cls_smul h

theorem line_smul_snd {a b : Fin 306936} (h : ¬Cm a b) {w : J} (hw : jR w = cls a * cls b) :
    w • b = third a b := by
  rw [← CFSG.Sporadic.Fi24.jR_smul, hw, mul_smul, cls_smul_self']
  rfl

theorem line_smul_third {a b : Fin 306936} (h : ¬Cm a b) {w : J} (hw : jR w = cls a * cls b) :
    w • third a b = a := by
  calc w • third a b = w • (w • b) := by rw [line_smul_snd h hw]
    _ = w • (w • (w • a)) := by rw [line_smul_fst h hw]
    _ = (w ^ 3) • a := by rw [pow_three, mul_smul, mul_smul]
    _ = a := by rw [line_cube h hw, one_smul]

end Lines

end CFSG.HardMathSupport.Dickson.I271.TabFi24
