module

public import CFSG.Dihedral.DisconnectedInvolutionGraph.CyclicPSubgroupOrder
public import Mathlib.Algebra.Order.Ring.Star

public section

namespace CFSG.DisconnectedInvolutionGraph.Helpers

variable {G : Type*} [Group G] [Finite G] [IsCyclic G]

theorem cyclic_two_pgroup_square_root (hpgroup : IsPGroup 2 G)
    (subgroup : Subgroup G) (hproper : subgroup < ⊤) (element : subgroup) :
    ∃ root : G, root ^ 2 = element.val := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : IsMulCommutative G := inferInstance
  let _ : CommGroup G := { (inferInstance : Group G) with mul_comm := mul_comm' }
  let square : G →* G := powMonoidHom 2
  obtain ⟨groupExponent, hgroupCard⟩ := IsPGroup.iff_card.mp hpgroup
  obtain ⟨subgroupExponent, hsubgroupCard⟩ := IsPGroup.iff_card.mp (hpgroup.to_subgroup subgroup)
  have hcardLt : Nat.card subgroup < Nat.card G := by
    have hcardLe : Nat.card subgroup ≤ Nat.card G :=
      Nat.le_of_dvd Nat.card_pos subgroup.card_subgroup_dvd_card
    have hcardNe : Nat.card subgroup ≠ Nat.card G :=
      fun heq => hproper.ne ((subgroup.card_eq_iff_eq_top).mp heq)
    exact lt_of_le_of_ne hcardLe hcardNe
  have hexponentLt : subgroupExponent < groupExponent := by
    by_contra hnot
    have hle := pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ)) (Nat.le_of_not_gt hnot)
    rw [hgroupCard, hsubgroupCard] at hcardLt
    omega
  have hgroupDiv : 2 ∣ Nat.card G := by
    rw [hgroupCard]
    exact dvd_pow_self 2 (by omega)
  have hrangeCard : Nat.card square.range = Nat.card G / 2 := by
    rw [IsCyclic.card_powMonoidHom_range G, Nat.gcd_eq_right hgroupDiv]
  have hsubgroupDiv : Nat.card subgroup ∣ Nat.card square.range := by
    rw [hrangeCard, hgroupCard, hsubgroupCard]
    obtain ⟨difference, hdifference⟩ := Nat.exists_eq_add_of_lt hexponentLt
    rw [hdifference, Nat.add_assoc, pow_add, pow_succ]
    rw [← Nat.mul_assoc, Nat.mul_div_cancel _ (by decide : 0 < 2)]
    exact dvd_mul_right _ _
  have hle : subgroup ≤ square.range := cyclic_subgroup_le_of_card_dvd subgroup square.range hsubgroupDiv
  obtain ⟨root, hroot⟩ := hle element.property
  exact ⟨root, hroot⟩

end CFSG.DisconnectedInvolutionGraph.Helpers
