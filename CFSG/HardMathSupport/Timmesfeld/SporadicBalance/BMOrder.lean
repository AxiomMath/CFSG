module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BMShape

public section

open scoped commutatorElement

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.Proving

variable {p : ℕ} {S : Type*} [Group S]

theorem exists_mul_ne_mul_of_isSimpleGroup {G : Type*} [Group G] [IsSimpleGroup G] [Finite G]
    (hG : ¬ (Nat.card G).Prime) : ∃ a b : G, a * b ≠ b * a := by
  by_contra h
  push Not at h
  let _ : CommGroup G := { (inferInstance : Group G) with mul_comm := h }
  exact hG IsSimpleGroup.prime_card

theorem commutator_eq_self_of_isSimpleGroup {L : Subgroup S} (hL : IsSimpleGroup ↥L)
    (hnab : ∃ a b : ↥L, a * b ≠ b * a) : ⁅L, L⁆ = L := by
  refine commutator_eq_self_of_commutator_eq_top ?_
  rcases hL.eq_bot_or_eq_top_of_normal (commutator ↥L) with h | h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    have hm : ⁅a, b⁆ ∈ commutator ↥L := by
      rw [commutator_def]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    rw [h, Subgroup.mem_bot] at hm
    exact hab (commutatorElement_eq_one_iff_mul_comm.1 hm)
  · exact h

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance
