module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5DeltaLocalQuaternion
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.ComponentClassification.AschbacherTheorem5.DeltaLocal

variable {G : Type} [Group G]

structure FzSpShape (t x₁ x₂ lam : G) (T₂ : Subgroup G) (a₁₂ a₂₂ a₃₂ : G) : Prop where
  quat₁ : IsQ8Pair (x₁ * t) a₁₂
  quat₂ : IsQ8Pair (x₂ * t) a₂₂
  quat₃ : IsQ8Pair ((x₁ * x₂)⁻¹ * t) a₃₂
  sq_eq : ((x₁ * x₂)⁻¹ * t) ^ 2 = (x₁ * t) ^ 2 * (x₂ * t) ^ 2
  comm₁₂ : ∀ u ∈ ({x₁ * t, a₁₂} : Set G), ∀ v ∈ ({x₂ * t, a₂₂} : Set G), Commute u v
  comm₁₃ : ∀ u ∈ ({x₁ * t, a₁₂} : Set G), ∀ v ∈ ({(x₁ * x₂)⁻¹ * t, a₃₂} : Set G), Commute u v
  comm₂₃ : ∀ u ∈ ({x₂ * t, a₂₂} : Set G), ∀ v ∈ ({(x₁ * x₂)⁻¹ * t, a₃₂} : Set G), Commute u v
  lam_sq : lam ^ 2 = 1
  lam_a₁₁ : lam * (x₁ * t) * lam⁻¹ = x₂ * t
  lam_a₁₂ : lam * a₁₂ * lam⁻¹ = a₂₂
  lam_comm₃ : Commute lam ((x₁ * x₂)⁻¹ * t) ∧ Commute lam a₃₂
  gen : T₂ = closure {x₁ * t, a₁₂, x₂ * t, a₂₂, (x₁ * x₂)⁻¹ * t, a₃₂, lam}
  card : Nat.card T₂ = 2 ^ 9

@[expose] def fzR3 (t x₁ x₂ a₃₂ : G) : Subgroup G := closure {(x₁ * x₂)⁻¹ * t, a₃₂}

end CFSG.OddStandard.SmallF3.FritzII
