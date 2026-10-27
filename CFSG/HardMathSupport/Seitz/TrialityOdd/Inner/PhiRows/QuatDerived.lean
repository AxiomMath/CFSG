module

public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.QuatWeyl
public import CFSG.RankThree.PartOne.KGD.D4T36Torus

set_option linter.unusedSectionVars false

public section

namespace CFSG.HardMathSupport.Seitz.TrialityOdd.Inner

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Lattice
  CFSG.RankThree.PartOne.KGD CFSG.RankThree.PartOne.KE
open scoped Matrix


@[expose] def derC : List (Fin TwistTag.D4.tag.rank) := [2, 1]

@[expose] def derY1 : List (Fin TwistTag.D4.tag.rank) := [0, 2, 1, 3]

@[expose] def derY2 : List (Fin TwistTag.D4.tag.rank) := [2, 3, 2, 0]

@[expose] noncomputable def wElt (l : List (Fin TwistTag.D4.tag.rank)) : WeylGroup TwistTag.D4.tag :=
  (coxeterSystem TwistTag.D4.tag).wordProd l

theorem wElt_smul (l : List (Fin TwistTag.D4.tag.rank)) (x : Fin TwistTag.D4.tag.rank → ℤ) :
    wElt l • x = wordMat TwistTag.D4.tag l *ᵥ x :=
  wordProd_smul_eq_wordMat_mulVec TwistTag.D4.tag l x

theorem derC_comm : wordMat TwistTag.D4.tag derC * d4T36M (-1) =
    d4T36M (-1) * wordMat TwistTag.D4.tag derC := by decide +kernel

theorem derY1_comm : wordMat TwistTag.D4.tag derY1 * d4T36M (-1) =
    d4T36M (-1) * wordMat TwistTag.D4.tag derY1 := by decide +kernel

theorem derY2_comm : wordMat TwistTag.D4.tag derY2 * d4T36M (-1) =
    d4T36M (-1) * wordMat TwistTag.D4.tag derY2 := by decide +kernel

theorem derC_Y1 : wordMat TwistTag.D4.tag derC * wordMat TwistTag.D4.tag derY1 =
    quatMat (QuaternionGroup.a 1) * wordMat TwistTag.D4.tag derY1 *
      wordMat TwistTag.D4.tag derC := by decide +kernel

theorem derC_Y2 : wordMat TwistTag.D4.tag derC * wordMat TwistTag.D4.tag derY2 =
    quatMat (QuaternionGroup.xa 0) * wordMat TwistTag.D4.tag derY2 *
      wordMat TwistTag.D4.tag derC := by decide +kernel

theorem wElt_C_Y1 : wElt derC * wElt derY1 = quatHom (QuaternionGroup.a 1) * wElt derY1 * wElt derC := by
  refine eq_of_smul_eq_smul (α := Fin TwistTag.D4.tag.rank → ℤ) fun x => ?_
  simp only [mul_smul, quatHom_apply, quatElt_smul, wElt_smul, Matrix.mulVec_mulVec]
  rw [derC_Y1, Matrix.mul_assoc]

theorem wElt_C_Y2 : wElt derC * wElt derY2 =
    quatHom (QuaternionGroup.xa 0) * wElt derY2 * wElt derC := by
  refine eq_of_smul_eq_smul (α := Fin TwistTag.D4.tag.rank → ℤ) fun x => ?_
  simp only [mul_smul, quatHom_apply, quatElt_smul, wElt_smul, Matrix.mulVec_mulVec]
  rw [derC_Y2, Matrix.mul_assoc]

end CFSG.HardMathSupport.Seitz.TrialityOdd.Inner
