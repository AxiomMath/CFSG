module

public import CFSG.LocalAnalysis.ComponentClassification.InnAutDerived
public import CFSG.RankThree.PartTwo.KFacts.AutKinds

public section

namespace CFSG.ComponentClassification.OuterAutomorphisms

open CFSG.RankThree.PartTwo.KFacts
open scoped commutatorElement

theorem mem_innAutDerived_of_inner_inv_of_odd {G : Type} [Group G]
    {α τ : MulAut G} {p : ℕ} (hp : Odd p) (hpow : α ^ p = 1)
    (hinn : IsInnerAut (τ * α * τ⁻¹ * α)) : α ∈ innAutDerived G := by
  have hc : ⁅τ, α⁆ ∈ commutator (MulAut G) := by
    rw [commutator_def]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  have hprod : ⁅τ, α⁆ * α ^ 2 = τ * α * τ⁻¹ * α := by
    rw [commutatorElement_def]
    group
  have hinner : ⁅τ, α⁆ * α ^ 2 ∈ innAutDerived G :=
    inner_le_innAutDerived G (hprod ▸ hinn)
  have hα2 : α ^ 2 ∈ innAutDerived G := by
    have hα2eq : α ^ 2 = (⁅τ, α⁆)⁻¹ * (⁅τ, α⁆ * α ^ 2) := by group
    rw [hα2eq]
    exact (innAutDerived G).mul_mem ((innAutDerived G).inv_mem
      (commutator_le_innAutDerived G hc)) hinner
  obtain ⟨k, rfl⟩ := hp
  have h2k : 2 * ((2 * k + 1 + 1) / 2) = 2 * k + 1 + 1 := by
    rw [show 2 * k + 1 + 1 = 2 * (k + 1) by ring]
    rw [Nat.mul_div_cancel_left (k + 1) (by norm_num : 0 < 2)]
  have hα : α = (α ^ 2) ^ ((2 * k + 1 + 1) / 2) := by
    rw [← pow_mul, h2k, pow_succ, hpow, one_mul]
  rw [hα]
  exact (innAutDerived G).pow_mem hα2 _

end CFSG.ComponentClassification.OuterAutomorphisms

end
