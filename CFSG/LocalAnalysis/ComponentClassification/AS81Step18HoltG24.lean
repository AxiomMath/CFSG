module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3Model
public import CFSG.LocalAnalysis.ComponentClassification.AS81Step13Basic
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard
open CFSG.ComponentClassification.RankTwoSporadic (IsActionHom)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem two_le_twoRank_of_sec3 {A A₁ R : Subgroup G} {g : G} {E F : Subgroup G} {x : G}
    (hS : Sec3Setting G A A₁ R g E F x) {H : Subgroup G} (hAH : A ≤ H) : 2 ≤ twoRank ↥H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, hEA, -, h16, -⟩ := Sec3.frame_inf_A₁ hS
  have hk' : Nat.card ((E ⊓ A₁).subgroupOf H) = 2 ^ 4 := by
    rw [show (2 : ℕ) ^ 4 = 16 by norm_num, ← h16]
    exact Nat.card_congr (subgroupOfEquivOfLe ((inf_le_right.trans hS.le).trans hAH)).toEquiv
  exact (by norm_num : 2 ≤ 4).trans
    (CFSG.SectionRank.le_pRank one_lt_two le_top (isElemAbelian_subgroupOf hEA H) hk')

end CFSG.ComponentClassification.AS81
