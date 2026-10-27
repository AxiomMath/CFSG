module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.XbarSetup

public section

namespace CFSG.EvenSporadicStandard.M23Std

open Subgroup CFSG.Open

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {F L1 N : Subgroup G}

namespace Setup

variable (S : Setup L z t F L1 N)

include S

theorem orderOf_zbar : orderOf (QuotientGroup.mk S.zX : Xbar L1) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine orderOf_eq_prime ?_ ?_
  · rw [pow_two, ← QuotientGroup.mk_mul]
    have : S.zX * S.zX = 1 := Subtype.ext (by simpa using S.one.z_mul_self)
    rw [this, QuotientGroup.mk_one]
  · intro h
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h
    have hLF : L1 ≤ F := fun x hx => S.L1_cz x hx (by
      have := (mem_centralizer_iff.1 h x hx).symm
      rwa [S.coe_zX] at this)
    have h1 := Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le hLF)
    rw [S.L1_card, S.nd.F_card] at h1
    omega

end Setup

end CFSG.EvenSporadicStandard.M23Std
