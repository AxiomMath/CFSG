module

public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOneNormalizerLagMain
public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOneNormalizerSetup

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64.EpsOne

open Subgroup Module Matrix SymplecticFlag CFSG.Assembly.LowTwoRank RadicalLabels FusionOrbits
open LinearMap (BilinForm)
open scoped Pointwise

theorem not_le_of_sylow_card {X : Type*} [Group X] [Finite X] {N T : Subgroup X}
    (S : Sylow 2 N) (hS : Nat.card S = 2 ^ 16) (hT : Nat.card T = 2 ^ 17) : ¬ T ≤ N := by
  intro hTN
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 (T.subgroupOf N) := IsPGroup.of_card (n := 17) (by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTN).toEquiv, hT])
  obtain ⟨P, hP⟩ := hp.exists_le_sylow
  have h1 : Nat.card P = Nat.card S := by
    rw [Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity]
  have h2 := Subgroup.card_le_of_le hP
  rw [h1, hS, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTN).toEquiv, hT] at h2
  norm_num at h2

theorem epsOneLagrangian_of_point (hP : EpsOnePointNormalizerStmt) :
    EpsOneLagrangianNormalizerStmt := by
  intro G _ _ hG L hL hLn hZ hmodel T hT z hzT hz hH V _ _ _ b hb hnd hV φ e he hfull u f E n Q r τ
    θ₁ N₂ D₂ F₂ H N₂₀ A₁ D₁ E₂ C₂ ν₂ hlam hexp κ Q₂ Dhat₂
  obtain ⟨hzC, σ, -, hinf, hbase, hE₂⟩ :=
    lagBase_of_setting hG hL hLn hZ hmodel T hT hzT hz hH hb hnd hV φ e he hfull hlam hexp
  have hpt := hP G hG L hL hLn hZ hmodel T hT z hzT hz hH V b hb hnd hV φ e he hfull hlam hexp
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨S₂', hS₂'⟩, -, hS₂card, -, -, -,
    -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨T₂, -, -,
    hT₂Q, hT₂card⟩⟩ := hpt
  have hS₂c : Nat.card S₂' = 2 ^ 16 := by
    rw [Nat.card_congr (Subgroup.equivMapOfInjective _ _ (Subgroup.subtype_injective _)).toEquiv,
      hS₂']
    exact hS₂card
  have hnot := not_le_of_sylow_card S₂' hS₂c hT₂card
  obtain ⟨x, hxT, hxN⟩ := Set.not_subset.1 hnot
  have hdata : LagData he φ hzC hz D₂ C₂ E₂ ν₂ σ := ⟨hbase, ⟨x, hT₂Q hxT, hxN⟩⟩
  exact ⟨hE₂, lagrangian_core hdata hinf⟩

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64.EpsOne
