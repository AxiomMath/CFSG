module

public import CFSG.GH74.Uniqueness.SU.SU4Sylow
public import CFSG.GH74.Uniqueness.SU.SU13TA2Cent
public import CFSG.GH74.Uniqueness.SU.SU13TA9Cfg

public section

namespace CFSG.GH74.Uniqueness.SU.SU13.TA.L9

open Equiv Equiv.Perm Subgroup CFSG.GH74.Uniqueness.SU.SU13.TA CFSG.GH74.Uniqueness.SU.SU4

variable {H : Type} [Group H] {π : H →* alternatingGroup (Fin 9)}

theorem odd_orderOf_s₃ (c : Cfg π) : Odd (orderOf c.s₃) := by
  have hne : c.s₃ ≠ 1 := fun h => by
    have := c.π_s₃
    rw [h, map_one] at this
    exact ea_mul_eb_mul_ec_ne_one this.symm
  have := orderOf_eq_prime (hp := ⟨Nat.prime_three⟩) c.s₃_pow hne
  rw [this]
  decide

theorem odd_orderOf_s₂ (c : Cfg π) : Odd (orderOf c.s₂) := by
  have hne : c.s₂ ≠ 1 := fun h => by
    have := c.π_s₂
    rw [h, map_one] at this
    exact ea_mul_eb_ne_one this.symm
  have := orderOf_eq_prime (hp := ⟨Nat.prime_three⟩) c.s₂_pow hne
  rw [this]
  decide

theorem card_centralizer_s₃ (hπ : TwoCover π) (c : Cfg π) :
    Nat.card ↥(centralizer ({c.s₃} : Set H)) = 162 := by
  rw [hπ.card_centralizer_singleton (odd_orderOf_s₃ c), c.π_s₃,
    card_centralizer_ea_mul_eb_mul_ec]

theorem isSylowIn_s₃ (hπ : TwoCover π) (c : Cfg π) {z : H} (hz : z ∈ π.ker) (hz1 : z ≠ 1) :
    IsSylowIn (centralizer ({c.s₃} : Set H) ⊓ centralizer ({z} : Set H)) (zpowers z) := by
  have := hπ.finite'
  have hzcen : ∀ g : H, g * z = z * g := Subgroup.mem_center_iff.mp (hπ.ker_le_center hz)
  have hzz : centralizer ({z} : Set H) = ⊤ := by
    rw [eq_top_iff]
    intro g _
    exact Subgroup.mem_centralizer_singleton_iff.mpr (hzcen g)
  have hz2 : z ^ 2 = 1 := hπ.sq_eq_one_of_mem_ker' hz
  have hle : zpowers z ≤ centralizer ({c.s₃} : Set H) ⊓ centralizer ({z} : Set H) := by
    rw [hzz, inf_top_eq, Subgroup.zpowers_le]
    exact Subgroup.mem_centralizer_singleton_iff.mpr (hzcen c.s₃).symm
  refine (isSylowIn_iff_card).mpr ⟨hle, 1, 81, ?_, by decide, ?_⟩
  · rw [Nat.card_zpowers, orderOf_eq_prime (hp := ⟨Nat.prime_two⟩) hz2 hz1]
    norm_num
  · rw [hzz, inf_top_eq, card_centralizer_s₃ hπ c]
    norm_num

end CFSG.GH74.Uniqueness.SU.SU13.TA.L9
