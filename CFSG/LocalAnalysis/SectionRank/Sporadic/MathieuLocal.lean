
module


public import CFSG.LocalAnalysis.SectionRank.Sporadic.LocalWitness
public import Certificates.Certificate8026

public section

namespace CFSG.SectionRank

open CFSG.Blueprint
open scoped commutatorElement

theorem M12_sylow3_cubic_witness :
    ∃ x y h : NativeSporadic.M12,
      x ^ 3 = 1 ∧ y ^ 3 = 1 ∧ ⁅x, y⁆ ≠ 1 ∧ Commute ⁅x, y⁆ x ∧ Commute ⁅x, y⁆ y ∧
      Nat.card (Subgroup.closure ({x, y} : Set NativeSporadic.M12)) = 3 ^ 3 ∧
      h * x * h⁻¹ = x ^ 2 * y ^ 0 * ⁅x, y⁆ ^ 1 ∧
      h * y * h⁻¹ = x ^ 0 * y ^ 2 * ⁅x, y⁆ ^ 1 ∧
      h * ⁅x, y⁆ * h⁻¹ = ⁅x, y⁆ ^ 1 := by
  obtain ⟨hx, hy, hz, hzx, hzy, hinj, h1, h2, h3⟩ := Certificates.certificate8026.1
  exact ⟨_, _, _, hx, hy, hz, hzx, hzy,
    LocalWitness.card_closure_eq_cube (by norm_num) hx hy hzx hzy hinj, h1, h2, h3⟩

theorem M24_sylow3_cubic_witness :
    ∃ x y h : NativeSporadic.M24,
      x ^ 3 = 1 ∧ y ^ 3 = 1 ∧ ⁅x, y⁆ ≠ 1 ∧ Commute ⁅x, y⁆ x ∧ Commute ⁅x, y⁆ y ∧
      Nat.card (Subgroup.closure ({x, y} : Set NativeSporadic.M24)) = 3 ^ 3 ∧
      h * x * h⁻¹ = x ^ 0 * y ^ 1 * ⁅x, y⁆ ^ 0 ∧
      h * y * h⁻¹ = x ^ 2 * y ^ 0 * ⁅x, y⁆ ^ 0 ∧
      h * ⁅x, y⁆ * h⁻¹ = ⁅x, y⁆ ^ 1 := by
  obtain ⟨hx, hy, hz, hzx, hzy, hinj, h1, h2, h3⟩ := Certificates.certificate8026.2
  exact ⟨_, _, _, hx, hy, hz, hzx, hzy,
    LocalWitness.card_closure_eq_cube (by norm_num) hx hy hzx hzy hinj, h1, h2, h3⟩

end CFSG.SectionRank
