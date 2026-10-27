module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

theorem inFStar_isQuasisimple {I : Subgroup G} (h : InFStar I) : CFSG.IsQuasisimple I := by
  unfold InFStar IsFStarGroup IsFGroup at h
  rcases h with ⟨hq, -⟩ | ⟨hq, -⟩ <;> exact hq

theorem orderOf_quaternion_a_two : orderOf (QuaternionGroup.a 2 : QuaternionGroup 2) = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (by decide) (by decide)

theorem natCard_range_quaternion {Y : Type} [Group Y] {f : QuaternionGroup 2 →* Y}
    (hf : Function.Injective f) : Nat.card f.range = 8 := by
  rw [← Nat.card_congr (MonoidHom.ofInjective hf).toEquiv, Nat.card_eq_fintype_card]
  decide

end CFSG.OddStandard.SmallF3.Omega
