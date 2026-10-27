module

public import Mathlib.GroupTheory.Sylow
import CFSG.FeitThompson.Foundations.SubgroupOrderAndIndex

open Pointwise

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

theorem factorization_eq_of_eq_pow_mul {n p a m : ℕ} (hp : p.Prime) (hm : ¬ p ∣ m)
    (hn : n = p ^ a * m) : n.factorization p = a := by
  have hm0 : m ≠ 0 := fun h => hm (h ▸ dvd_zero p)
  rw [hn, Nat.factorization_mul (pow_ne_zero _ hp.pos.ne') hm0]
  simp [hp.factorization_pow, Nat.factorization_eq_zero_of_not_dvd hm]

variable {G : Type*} [Group G] [Finite G] {p a m : ℕ}

theorem natCard_sylow_eq_pow (hp : p.Prime) (hm : ¬ p ∣ m) (hG : Nat.card G = p ^ a * m)
    (P : Sylow p G) : Nat.card (P : Subgroup G) = p ^ a := by
  have : Fact p.Prime := ⟨hp⟩
  rw [P.card_eq_multiplicity, factorization_eq_of_eq_pow_mul hp hm hG]

theorem exists_subgroup_natCard_eq_pow (hp : p.Prime) (hm : ¬ p ∣ m)
    (hG : Nat.card G = p ^ a * m) : ∃ H : Subgroup G, Nat.card H = p ^ a := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow p G))
  exact ⟨(P : Subgroup G), natCard_sylow_eq_pow hp hm hG P⟩

theorem exists_sylow_natCard_eq_pow (hp : p.Prime) (hm : ¬ p ∣ m)
    (hG : Nat.card G = p ^ a * m) : ∃ P : Sylow p G, Nat.card (P : Subgroup G) = p ^ a := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow p G))
  exact ⟨P, natCard_sylow_eq_pow hp hm hG P⟩

theorem index_sylow_eq (hp : p.Prime) (hm : ¬ p ∣ m) (hG : Nat.card G = p ^ a * m)
    (P : Sylow p G) : (P : Subgroup G).index = m := by
  have h : Nat.card G = (P : Subgroup G).index * Nat.card (P : Subgroup G) := by
    rw [← natCard_range_leftCoset, natCard_eq_natCard_range_leftCoset_mul_natCard]
  rw [natCard_sylow_eq_pow hp hm hG P, hG, mul_comm (p ^ a) m] at h
  exact (Nat.eq_of_mul_eq_mul_right (pow_pos hp.pos a) h).symm

theorem exists_sylow_coe_eq_of_natCard_eq_pow (hp : p.Prime) (hm : ¬ p ∣ m)
    (hG : Nat.card G = p ^ a * m) {H : Subgroup G} (hH : Nat.card H = p ^ a) :
    ∃ P : Sylow p G, (P : Subgroup G) = H := by
  have : Fact p.Prime := ⟨hp⟩
  exact ⟨Sylow.ofCard H (by rw [hH, factorization_eq_of_eq_pow_mul hp hm hG]), rfl⟩

end

end CFSG.FeitThompson
