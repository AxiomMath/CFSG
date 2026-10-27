module

public import CFSG.Adapters.Involutions

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem exists_conj_mem_sylow_ne_of_isSimpleGroup (hG : IsSimpleGroup G)
    (h4 : 4 ∣ Nat.card G) (S : Sylow 2 G) {z : G} (hzS : z ∈ (S : Subgroup G))
    (hz2 : orderOf z = 2) (hzc : ∀ s ∈ (S : Subgroup G), s * z = z * s) :
    ∃ g : G, g⁻¹ * z * g ∈ (S : Subgroup G) ∧ g⁻¹ * z * g ≠ z := by
  by_contra h
  push Not at h
  have hzZ : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G) := by
    rw [Subgroup.mem_center_iff]
    intro s
    exact Subtype.ext (hzc s.1 s.2)
  have hzord : orderOf (⟨z, hzS⟩ : (S : Subgroup G)) = 2 := by
    rw [Subgroup.orderOf_mk, hz2]
  have hcen : (QuotientGroup.mk z : G ⧸ CFSG.oddCore G) ∈
      Subgroup.center (G ⧸ CFSG.oddCore G) :=
    (CFSG.Adapters.glauberman_zStar S ⟨z, hzS⟩ hzZ hzord h).2
  haveI : IsSimpleGroup G := hG
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (CFSG.oddCore G) with hbot | htop
  ·
    have hzcenter : z ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro g
      have hq : (QuotientGroup.mk g : G ⧸ CFSG.oddCore G) * QuotientGroup.mk z =
          QuotientGroup.mk z * QuotientGroup.mk g :=
        Subgroup.mem_center_iff.mp hcen (QuotientGroup.mk g)
      have hq' : (QuotientGroup.mk (g * z) : G ⧸ CFSG.oddCore G) =
          QuotientGroup.mk (z * g) := by
        simpa only [QuotientGroup.mk_mul] using hq
      have hmem : (g * z)⁻¹ * (z * g) ∈ CFSG.oddCore G := QuotientGroup.eq.mp hq'
      rw [hbot] at hmem
      have heq : (g * z)⁻¹ * (z * g) = 1 := Subgroup.mem_bot.mp hmem
      have hzg : z * g = g * z := by
        apply mul_left_cancel (a := (g * z)⁻¹)
        rw [heq, inv_mul_cancel]
      exact hzg.symm
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with hcbot | hctop
    · have hz1 : z = 1 := by
        rw [hcbot] at hzcenter
        exact Subgroup.mem_bot.mp hzcenter
      rw [hz1, orderOf_one] at hz2
      exact absurd hz2 (by norm_num)
    ·
      haveI : IsMulCommutative G := Subgroup.center_eq_top_iff.mp hctop
      have hp : (Nat.card G).Prime :=
        (Group.is_simple_iff_prime_card (α := G)).mp ‹IsSimpleGroup G›
      rcases hp.eq_one_or_self_of_dvd 4 h4 with h41 | h4G
      · norm_num at h41
      · rw [← h4G] at hp
        exact (by norm_num : ¬ Nat.Prime 4) hp
  ·
    exact CFSG.Adapters.not_mem_oddCore_of_orderOf_eq_two hz2 (htop ▸ Subgroup.mem_top z)

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
