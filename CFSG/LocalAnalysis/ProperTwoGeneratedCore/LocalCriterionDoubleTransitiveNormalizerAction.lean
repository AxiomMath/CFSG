module

public import CFSG.Assembly.Defs
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionCentralizerTripleTransportAction
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionMaximalPrimeFixedSets
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointOddCore

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionDoubleTransitiveNormalizer

open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime
open CFSG.ProperTwoGeneratedCore.LocalCriterionCentralizerTripleTransport

variable {G : Type*} [Group G]

@[expose, instance_reducible] def pointRightCosetOppositeMulAction (H : Subgroup G) :
    MulAction Gᵐᵒᵖ (pointRightCosetSpace H) where
  smul g a := pointRightCosetMul H a g.unop
  one_smul a := pointRightCosetMul_one H a
  mul_smul g k a := (pointRightCosetMul_mul H a k.unop g.unop).symm

attribute [local instance] pointRightCosetOppositeMulAction

theorem point_rightAct_eq (H : Subgroup G) (a : pointRightCosetSpace H) (g : G) :
    rightAct a g = pointRightCosetMul H a g := rfl

theorem point_rightStabilizer_eq (H : Subgroup G) (a : pointRightCosetSpace H) :
    rightStabilizer a = rightCosetStabilizer H a := by
  ext g
  exact (mem_rightStabilizer a g).trans (mem_point_right_stabilizer_iff H a g).symm

theorem point_rightFixedSet_eq (H A : Subgroup G) :
    rightFixedSet A = pointFixedSet H A := rfl

theorem point_tripleStabilizer_eq (H : Subgroup G) (z : G)
    (beta : pointRightCosetSpace H) :
    tripleStabilizer z (rightCosetMk H 1) beta = triplePointStabilizer H z beta := by
  rw [tripleStabilizer, point_rightStabilizer_eq, point_rightStabilizer_eq,
    point_rightStabilizer_eq, rightCosetStabilizer_base]
  change H ⊓ rightCosetStabilizer H beta ⊓
    rightCosetStabilizer H (pointRightCosetMul H beta z) = _
  rw [pointRightCosetMul_eq_translate, triplePointStabilizer, pairPointStabilizer,
    rightCosetStabilizer_base]

end CFSG.ProperTwoGeneratedCore.LocalCriterionDoubleTransitiveNormalizer
