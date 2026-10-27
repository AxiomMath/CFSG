module

import CFSG.LocalAnalysis.SteinbergBMEvenG2FixedNoNormalSL2
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.Assembly.LowTwoRank

theorem gomi_card_eqLocus_congr {A B : Type*} [Group A] [Group B] (φ : A ≃* B) (α : MulAut A) :
    Nat.card ↥((MulAut.congr φ α).toMonoidHom.eqLocus (MonoidHom.id B)) =
      Nat.card ↥(α.toMonoidHom.eqLocus (MonoidHom.id A)) := by
  rw [← CFSG.LocalAnalysis.SteinbergBM.map_eqLocus_mulAut_congr φ α]
  exact Subgroup.card_map_of_injective φ.injective

variable {X : Type} [Group X] [Finite X] {J D E : Subgroup X} {a : X}

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
