module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotLeviSp6B3
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotLeviSp6Hom
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType CFSG.LieType.Steinberg CFSG.Assembly.LowTwoRank
  CFSG.Timmesfeld.LieEmbed
open CFSG.LieType.Ree (ReeTag)
open CFSG.LieType.Chevalley (finiteExceptionalAut_pinnedX_long finiteExceptionalAut_pinnedX_short)

local instance f4PilotGraphSpinModelF4NeZeroRankF4 : NeZero Tag.F4.rank := ⟨by decide⟩

local instance f4PilotGraphSpinModelF4NeZeroRankReeF4 : NeZero ReeTag.F4.tag.rank := ⟨by decide⟩

theorem f4_nodes_one_two_check :
    ReeTag.F4.quadForm (Pi.single 1 1 : Fin Tag.F4.rank → ℤ) = 2 * ReeTag.F4.prime ∧
      ReeTag.F4.quadForm (-Pi.single 1 1 : Fin Tag.F4.rank → ℤ) = 2 * ReeTag.F4.prime ∧
      ReeTag.F4.quadForm (Pi.single 2 1 : Fin Tag.F4.rank → ℤ) = 2 ∧
      ReeTag.F4.quadForm (-Pi.single 2 1 : Fin Tag.F4.rank → ℤ) = 2 ∧
      ReeTag.F4.dualRoot (Pi.single 1 1 : Fin Tag.F4.rank → ℤ) = Pi.single 2 1 ∧
      ReeTag.F4.dualRoot (-Pi.single 1 1 : Fin Tag.F4.rank → ℤ) = -Pi.single 2 1 ∧
      ReeTag.F4.dualRoot (Pi.single 2 1 : Fin Tag.F4.rank → ℤ) = Pi.single 1 1 ∧
      ReeTag.F4.dualRoot (-Pi.single 2 1 : Fin Tag.F4.rank → ℤ) = -Pi.single 1 1 := by
  decide +kernel

section Par


variable {K : Type} [Field K] [CharP K 2]

theorem f4Par_eq_pinnedX_charTwo {γ : Fin Tag.F4.rank → ℤ} (hγ : IsRoot .F4 γ) (c : K) :
    Adjoint.f4Par K γ c = ⟨pinnedX .F4 K γ c, pinnedX_mem_adjointGroup γ c⟩ := by
  apply Subtype.ext
  rw [coe_f4Par_eq_pinnedX hγ]
  rcases (Chevalley.rootOperatorFamily .F4).pinnedFamilySign_eq γ with h | h <;> rw [h]
  · rw [Int.cast_one, one_mul]
  · rw [Int.cast_neg, Int.cast_one, CharTwo.neg_eq, one_mul]

variable
  [Finite K]

theorem c3LeviEquiv_x_single_two (c : K) :
    ((c3LeviEquiv K (Sp.x 3 K (Pi.single 2 1) c) : C3Levi K) : adjointGroup .F4 K) =
      ⟨pinnedX .F4 K (Pi.single 1 1) c, pinnedX_mem_adjointGroup _ c⟩ := by
  rw [c3LeviEquiv_x, c3ToF4_single, f4Par_eq_pinnedX_charTwo (isRoot_single _ _)]
  rfl

theorem c3LeviEquiv_x_neg_single_two (c : K) :
    ((c3LeviEquiv K (Sp.x 3 K (-Pi.single 2 1) c) : C3Levi K) : adjointGroup .F4 K) =
      ⟨pinnedX .F4 K (-Pi.single 1 1) c, pinnedX_mem_adjointGroup _ c⟩ := by
  rw [c3LeviEquiv_x, map_neg, c3ToF4_single, f4Par_eq_pinnedX_charTwo (isRoot_neg_single _ _)]
  rfl

theorem c3LeviEquiv_x_single_one (c : K) :
    ((c3LeviEquiv K (Sp.x 3 K (Pi.single 1 1) c) : C3Levi K) : adjointGroup .F4 K) =
      ⟨pinnedX .F4 K (Pi.single 2 1) c, pinnedX_mem_adjointGroup _ c⟩ := by
  rw [c3LeviEquiv_x, c3ToF4_single, f4Par_eq_pinnedX_charTwo (isRoot_single _ _)]
  rfl

theorem c3LeviEquiv_x_neg_single_one (c : K) :
    ((c3LeviEquiv K (Sp.x 3 K (-Pi.single 1 1) c) : C3Levi K) : adjointGroup .F4 K) =
      ⟨pinnedX .F4 K (-Pi.single 2 1) c, pinnedX_mem_adjointGroup _ c⟩ := by
  rw [c3LeviEquiv_x, map_neg, c3ToF4_single, f4Par_eq_pinnedX_charTwo (isRoot_neg_single _ _)]
  rfl

end Par

section Graph


variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]

theorem graphAutF4_pinnedX_single_one (c : K) :
    graphAutF4 K ⟨pinnedX .F4 K (Pi.single 1 1) c, pinnedX_mem_adjointGroup _ c⟩ =
      ⟨pinnedX .F4 K (Pi.single 2 1) c, pinnedX_mem_adjointGroup _ c⟩ := by
  have hl : (Pi.single 1 1 : Fin Tag.F4.rank → ℤ) ∈ ReeTag.F4.longRoots :=
    ⟨isRoot_single _ _, ReeTag.lengthParam_eq_prime_iff.2 f4_nodes_one_two_check.1⟩
  have e := finiteExceptionalAut_pinnedX_long (K := K) hl c
  rw [f4_nodes_one_two_check.2.2.2.2.1] at e
  exact e

theorem graphAutF4_pinnedX_neg_single_one (c : K) :
    graphAutF4 K ⟨pinnedX .F4 K (-Pi.single 1 1) c, pinnedX_mem_adjointGroup _ c⟩ =
      ⟨pinnedX .F4 K (-Pi.single 2 1) c, pinnedX_mem_adjointGroup _ c⟩ := by
  have hl : (-Pi.single 1 1 : Fin Tag.F4.rank → ℤ) ∈ ReeTag.F4.longRoots :=
    ⟨isRoot_neg_single _ _, ReeTag.lengthParam_eq_prime_iff.2 f4_nodes_one_two_check.2.1⟩
  have e := finiteExceptionalAut_pinnedX_long (K := K) hl c
  rw [f4_nodes_one_two_check.2.2.2.2.2.1] at e
  exact e

theorem graphAutF4_pinnedX_single_two (c : K) :
    graphAutF4 K ⟨pinnedX .F4 K (Pi.single 2 1) c, pinnedX_mem_adjointGroup _ c⟩ =
      ⟨pinnedX .F4 K (Pi.single 1 1) (c ^ 2), pinnedX_mem_adjointGroup _ _⟩ := by
  have hs : (Pi.single 2 1 : Fin Tag.F4.rank → ℤ) ∈ ReeTag.F4.shortRoots :=
    ⟨isRoot_single _ _, ReeTag.lengthParam_eq_one_iff.2 f4_nodes_one_two_check.2.2.1⟩
  have e := finiteExceptionalAut_pinnedX_short (K := K) hs c
  rw [f4_nodes_one_two_check.2.2.2.2.2.2.1] at e
  exact e

theorem graphAutF4_pinnedX_neg_single_two (c : K) :
    graphAutF4 K ⟨pinnedX .F4 K (-Pi.single 2 1) c, pinnedX_mem_adjointGroup _ c⟩ =
      ⟨pinnedX .F4 K (-Pi.single 1 1) (c ^ 2), pinnedX_mem_adjointGroup _ _⟩ := by
  have hs : (-Pi.single 2 1 : Fin Tag.F4.rank → ℤ) ∈ ReeTag.F4.shortRoots :=
    ⟨isRoot_neg_single _ _, ReeTag.lengthParam_eq_one_iff.2 f4_nodes_one_two_check.2.2.2.1⟩
  have e := finiteExceptionalAut_pinnedX_short (K := K) hs c
  rw [f4_nodes_one_two_check.2.2.2.2.2.2.2] at e
  exact e

end Graph

end CFSG.SeitzReduction.F4Pilot
