module

public import CFSG.RankThree.PartOne.KE.CTStatement
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.PartOne.KGD.D4Weyl

set_option linter.unusedSectionVars false

public section

namespace CFSG.HardMathSupport.Seitz.TrialityOdd.Inner

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Lattice
  CFSG.RankThree.PartOne.KGD CFSG.RankThree.PartOne.KE
open scoped Matrix

@[expose] def quatU : List (Fin TwistTag.D4.tag.rank) := [2, 3, 0, 2, 1, 0]

@[expose] def quatV : List (Fin TwistTag.D4.tag.rank) := [3, 2, 1, 0, 2, 0]

@[expose] def quatWord : QuaternionGroup 2 → List (Fin TwistTag.D4.tag.rank)
  | .a i => (List.replicate i.val quatU).flatten
  | .xa i => quatV ++ (List.replicate i.val quatU).flatten

@[expose] def quatMat (g : QuaternionGroup 2) :
    Matrix (Fin TwistTag.D4.tag.rank) (Fin TwistTag.D4.tag.rank) ℤ :=
  wordMat TwistTag.D4.tag (quatWord g)

theorem quatMat_mul : ∀ g h : QuaternionGroup 2, quatMat (g * h) = quatMat g * quatMat h := by
  decide +kernel

theorem quatMat_a_two : quatMat (QuaternionGroup.a 2) = -1 := by decide +kernel

@[expose] noncomputable def quatElt (g : QuaternionGroup 2) : WeylGroup TwistTag.D4.tag :=
  (coxeterSystem TwistTag.D4.tag).wordProd (quatWord g)

theorem quatElt_smul (g : QuaternionGroup 2) (x : Fin TwistTag.D4.tag.rank → ℤ) :
    quatElt g • x = quatMat g *ᵥ x :=
  wordProd_smul_eq_wordMat_mulVec TwistTag.D4.tag (quatWord g) x

theorem quatElt_mul (g h : QuaternionGroup 2) : quatElt (g * h) = quatElt g * quatElt h := by
  refine eq_of_smul_eq_smul (α := Fin TwistTag.D4.tag.rank → ℤ) fun x => ?_
  rw [mul_smul, quatElt_smul, quatElt_smul, quatElt_smul, quatMat_mul, Matrix.mulVec_mulVec]

@[expose] noncomputable def quatHom : QuaternionGroup 2 →* WeylGroup TwistTag.D4.tag :=
  MonoidHom.mk' quatElt quatElt_mul

theorem quatHom_apply (g : QuaternionGroup 2) : quatHom g = quatElt g := rfl

theorem quatHom_a_two_smul (x : Fin TwistTag.D4.tag.rank → ℤ) :
    quatHom (QuaternionGroup.a 2) • x = -x := by
  rw [quatHom_apply, quatElt_smul, quatMat_a_two, Matrix.neg_mulVec, Matrix.one_mulVec]

end CFSG.HardMathSupport.Seitz.TrialityOdd.Inner
