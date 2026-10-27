module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.Defs

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Signalizer
  CFSG.GH74.GLS.Stage2.Bender.Thm1
open scoped commutatorElement

section Twelve

variable {G : Type} [Group G] [Finite G]

theorem card_lt_of_lt' {H K : Subgroup G} (h : H < K) : Nat.card ↥H < Nat.card ↥K :=
  lt_of_le_of_ne (Subgroup.card_le_of_le h.le) (fun heq => h.ne (Subgroup.eq_of_le_of_card_ge h.le heq.ge))

omit [Finite G] in
theorem ne_top_of_isPGroup_three {z : G} (hz : orderOf z = 2) {A : Subgroup G} (hA : IsPGroup 3 ↥A) : A ≠ ⊤ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro htop
  have hzA : z ∈ A := htop ▸ Subgroup.mem_top z
  obtain ⟨n, hn⟩ := IsPGroup.iff_orderOf.mp hA ⟨z, hzA⟩
  rw [Subgroup.orderOf_mk, hz] at hn
  rcases Nat.eq_zero_or_pos n with h0 | h0
  · rw [h0] at hn
    norm_num at hn
  · have : 3 ∣ 2 := hn ▸ dvd_pow_self 3 (Nat.pos_iff_ne_zero.mp h0)
    omega

end Twelve

end CFSG.GH74.GLS.Stage2.Bender.Thm2
