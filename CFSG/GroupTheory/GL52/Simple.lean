module

public import CFSG.GroupTheory.GL52.Basic
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

public noncomputable section

namespace CFSG.GroupTheory.GL52

open Matrix

theorem card_G52 : Nat.card G52 = 2 ^ 10 * 3 ^ 2 * 5 * 7 * 31 := by
  rw [Matrix.card_GL_field, ZMod.card, Fin.prod_univ_five]
  norm_num

theorem det_G52 (g : G52) : (g : M5).det = 1 := by
  have h : (g : M5).det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det (g : M5)).1 g.isUnit).ne_zero
  have key : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by decide
  exact key _ h

theorem bijective_toGL_G52 :
    Function.Bijective
      (Matrix.SpecialLinearGroup.toGL : Matrix.SpecialLinearGroup (Fin 5) (ZMod 2) →* G52) :=
  ⟨Matrix.SpecialLinearGroup.toGL_injective, fun g =>
    ⟨⟨(g : M5), det_G52 g⟩, Units.ext (Matrix.SpecialLinearGroup.coe_GL_coe_matrix _)⟩⟩

theorem center_SL_five_two_eq_bot :
    Subgroup.center (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) = ⊥ := by
  refine eq_bot_iff.2 fun A hA => ?_
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hA
  have key : ∀ x : ZMod 2, x ^ 5 = 1 → x = 1 := by decide
  rw [Fintype.card_fin] at hr
  rw [Subgroup.mem_bot]
  ext i j
  rw [← hrA, key r hr]
  simp

@[expose] def G52EquivPSL : G52 ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 5) (ZMod 2) :=
  ((MulEquiv.ofBijective _ bijective_toGL_G52).symm.trans
    (QuotientGroup.quotientBot (G := Matrix.SpecialLinearGroup (Fin 5) (ZMod 2))).symm).trans
    (QuotientGroup.quotientMulEquivOfEq center_SL_five_two_eq_bot.symm)

theorem isSimpleGroup_G52 : IsSimpleGroup G52 := by
  have h := (CFSG.LinearGroups.linear_projective_simple (K := ZMod 2) (n := 5) (by norm_num)
    (Or.inl (by norm_num))).2.1
  exact G52EquivPSL.isSimpleGroup

@[expose] def transvE04 : G52 :=
  mk5 !![1, 0, 0, 0, 1; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1]
    !![1, 0, 0, 0, 1; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1] (by decide)

@[expose] def transvE40 : G52 :=
  mk5 !![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 1, 0, 0, 0, 1]
    !![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 1, 0, 0, 0, 1] (by decide)

theorem not_commutative_G52 : ¬ ∀ a b : G52, a * b = b * a := by
  intro h
  have e := congrArg (fun g : G52 => (g : M5)) (h transvE04 transvE40)
  simp only [Units.val_mul, transvE04, transvE40, coe_mk5] at e
  revert e
  decide

end CFSG.GroupTheory.GL52
