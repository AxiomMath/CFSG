module

public import CFSG.LieType.Chevalley.RankOneGaussian

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S19G

open CFSG.LieType.Chevalley Matrix
open scoped MatrixGroups commutatorElement

variable {F : Type} [Field F]

theorem commutatorElement_P_Q (h3 : (3 : F) = 0) :
    ⁅⁅uSL (1 : F), vSL (1 : F)⁆, ⁅uSL (1 : F), vSL (-1 : F)⁆⁆ = -1 := by
  apply SL2_ext <;>
    simp [commutatorElement_def, coe_uSL, coe_vSL, SpecialLinearGroup.coe_mul,
      SpecialLinearGroup.coe_inv, SpecialLinearGroup.coe_neg, adjugate_fin_two, mul_apply,
      Fin.sum_univ_two] <;>
    first
      | linear_combination (2 : F) * h3
      | linear_combination (-2 : F) * h3

theorem neg_one_mem_second_derived (h2 : (2 : F) ≠ 0) :
    (-1 : SL2 F) ∈ ⁅commutator (SL2 F), commutator (SL2 F)⁆ := by
  by_cases h : ∃ a : F, a ≠ 0 ∧ a ^ 2 ≠ 1
  · obtain ⟨a, ha, hasq⟩ := h
    rw [Matrix.SL2.commutator_eq_top ha hasq, ← commutator_def,
      Matrix.SL2.commutator_eq_top ha hasq]
    exact Subgroup.mem_top _
  · push Not at h
    have h3 : (3 : F) = 0 := by linear_combination h 2 h2
    rw [← commutatorElement_P_Q h3]
    exact Subgroup.commutator_mem_commutator
      (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))
      (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))

theorem map_neg_one_mem_second_derived (h2 : (2 : F) ≠ 0) {G : Type*} [Group G]
    (Φ : SL2 F →* G) : Φ (-1) ∈ ⁅⁅Φ.range, Φ.range⁆, ⁅Φ.range, Φ.range⁆⁆ := by
  have h := Subgroup.mem_map_of_mem Φ (neg_one_mem_second_derived h2)
  rwa [commutator_def, Subgroup.map_commutator, Subgroup.map_commutator,
    ← MonoidHom.range_eq_map] at h

end CFSG.ClassicalInvolution.Disconnected.AschTight.S19G
